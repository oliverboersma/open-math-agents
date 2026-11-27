#!/usr/bin/env bash
# Verdict for one finished check-proof run (trusted: never runs pull request code). Extracted unchanged from
# verdict.yml so the merger loop (backlog.yml) and verdict.yml share it.
# Needs: GH_TOKEN REPO RUN_URL RUN_ID RUN_ATTEMPT HEAD_SHA [OMA_SITE]; the current directory holds artifact/ (the run's
# verdict artifact) and base/ (main, with tools/ and data/).
set -euo pipefail
# Comments and labels go through REST: the GraphQL budget of GITHUB_TOKEN (about 1,000 points an hour for the whole
# repository) is kept for the merge itself.
comment() { gh api "repos/$REPO/issues/$PR/comments" -f body="$1" >/dev/null; }
# The merger (backlog.yml, tools/merger_loop.sh v2) is the only caller now; an older merger still running from before
# tools/merger.v2 existed must not report twice, so it does nothing here.
if [ -e base/tools/merger.v2 ] && [ -z "${MERGER_V2:-}" ]; then exit 0; fi
if [ -e base/tools/merger.v3 ] && [ -z "${MERGER_V3:-}" ]; then exit 0; fi   # the v3 merger has taken over
PR=$(head -c 12 artifact/pr.txt | tr -cd '0-9')
[ -n "$PR" ] || exit 0
gh api "repos/$REPO/pulls/$PR" > pr.json
[ "$(jq -r .state pr.json)" = open ] || exit 0   # merged or closed meanwhile: nothing to report
# The changed files and the checked file come from git (GitHub's merge ref of the pull request), which does not use
# the API budget; the API is the fallback when the merge ref is missing or not at the checked commit.
GITREF=0
if git -C base fetch -q --depth 2 origin "refs/pull/$PR/merge" 2>/dev/null \
   && [ "$(git -C base rev-parse FETCH_HEAD^2 2>/dev/null)" = "$HEAD_SHA" ]; then
  git -C base diff --name-status FETCH_HEAD^1 FETCH_HEAD > names.txt
  python3 -I -c '
import json
st = {"A": "added", "M": "modified", "D": "removed"}
rows = [l.rstrip("\n").split("\t") for l in open("names.txt") if l.strip()]
json.dump([{"filename": r[-1], "status": st.get(r[0][0], r[0])} for r in rows], open("files.json", "w"))'
  git -C base rev-parse FETCH_HEAD^1 > mergebase.txt   # main as GitHub merged it (parent shas kept: later fetches move FETCH_HEAD)
  GITREF=1
else
  gh api "repos/$REPO/pulls/$PR/files" > files.json
fi
python3 -I - <<'PY' > decision.txt
import json, os, re
pr = json.load(open("pr.json")); files = json.load(open("files.json")); v = json.load(open("artifact/verdict.json"))
cat = {p["id"]: p for p in json.load(open("base/data/catalog.json"))["problems"]}
verdict, reason = v.get("verdict", "fault"), v.get("reason", "")
st = files[0]["status"] if len(files) == 1 else ""
m = re.fullmatch(r"(proofs|reductions|statements)/([A-Za-z0-9_.'\-]+)\.lean", files[0]["filename"]) if st == "added" or (st == "modified" and files[0]["filename"].startswith("proofs/")) else None
path = files[0]["filename"] if m else ""
pid = m.group(2) if m else None
if pr["head"]["sha"] != os.environ["HEAD_SHA"]:
    verdict, reason = "stale", "the pull request changed after this check; a newer check will report"
elif not m or v.get("problem") not in (None, pid):
    verdict, reason = "rejected", "a pull request must add exactly one file proofs/<id>.lean, reductions/<id>.R<n>.lean or statements/<id>.lean"
print(verdict); print(path); print(v.get("kind", "")); print(v.get("polarity", "proof")); print(reason.replace("\n", " ")[:900]); print("replace" if st == "modified" else "new")
PY
mapfile -t D < decision.txt
VERDICT="${D[0]}"; FPATH="${D[1]}"; KIND="${D[2]}"; POL="${D[3]}"; REASON="${D[4]}"; MODE="${D[5]:-new}"
[ "$VERDICT" = "stale" ] && exit 0
PID="$(basename "$FPATH" .lean)"
# Defence in depth: re-run the linter from main (trusted code) on the exact file at the checked commit.
# Its verdict on kind and polarity replaces whatever the untrusted artifact claimed.
if [ "$VERDICT" = "accepted" ]; then
  # main moves every few seconds (merges): lint against its latest statements, reductions and catalogue, so a proof of a
  # problem whose statement was merged minutes ago is not refused for a missing statement
  git -C base fetch -q --depth 1 origin main 2>/dev/null && git -C base checkout -q FETCH_HEAD -- statements reductions data 2>/dev/null || true
  mkdir -p "base/$(dirname "$FPATH")"
  if [ "$MODE" = replace ]; then
    # Shortest-proof rule, re-checked here with trusted code: the proof on main right now against the checked one.
    if [ "$GITREF" = 1 ] && git -C base show "$(cat mergebase.txt):$FPATH" > old.lean 2>/dev/null; then :; else
      gh api "repos/$REPO/contents/$FPATH?ref=main" --jq .content | base64 -d > old.lean
    fi
  fi
  if [ "$GITREF" = 1 ] && git -C base show "$HEAD_SHA:$FPATH" > checked.lean 2>/dev/null; then
    cp checked.lean "base/$FPATH"
  else
    gh api "repos/$REPO/contents/$FPATH?ref=$HEAD_SHA" --jq .content | base64 -d > "base/$FPATH"
  fi
  if [ "$MODE" = replace ]; then
    read -r RES NEWLEN OLDLEN < <(python3 -I base/tools/prooflen.py old.lean "base/$FPATH")
    if [ "$RES" != shorter ]; then
      VERDICT=rejected; REASON="already proved: \`$FPATH\` is on main; a new proof replaces it only if it is at least 5% and 20 characters shorter, comments and spaces not counted (yours: $NEWLEN, current: $OLDLEN)"
    fi
  fi
  if [ "$VERDICT" != accepted ]; then :
  elif ! (cd base && python3 -I tools/lint.py "$FPATH" data/catalog.json > "${RELINT:-/tmp/relint.json}"); then
    VERDICT=rejected; REASON="lint (trusted re-check): $(python3 -I -c 'import json,os;print("; ".join(json.load(open(os.environ.get("RELINT","/tmp/relint.json")))["errors"]))')"
  else
    POL=$(python3 -I -c 'import json,os;print(json.load(open(os.environ.get("RELINT","/tmp/relint.json")))["polarity"])')
    KIND=$(python3 -I -c 'import json,os;d=json.load(open(os.environ.get("RELINT","/tmp/relint.json")));print(d["type"] if d["type"] in ("reduction","statement") else d["kind"])')
  fi
fi
case "$VERDICT" in
  accepted)
    # Everything Lean accepts is merged and credited at once (no human gate). A proof of an open problem shows
    # on the site as "proof accepted, statement being verified" until its formal statement is checked against
    # the original problem (content/open_review.json); a statement merged here is checked the same way.
    if [ "$MODE" = replace ]; then
      MSG="**ACCEPTED: shorter proof** of \`$PID\` ($NEWLEN characters against $OLDLEN, comments and spaces not counted). Merged: it replaces the previous proof, and you are credited with the shortest proof of this problem (the first solve stays with whoever proved it first). [Run]($RUN_URL)"
    elif [ "$KIND" = "statement" ]; then
      MSG="**ACCEPTED: the statement compiles.** Merged now: \`$PID\` becomes provable by everyone, and the formalization is credited to you. Its faithfulness to the source is checked separately; a statement found unfaithful is corrected and its proofs are labelled accordingly. [Run]($RUN_URL)"
    elif [ "$KIND" = "open" ]; then
      MSG="**ACCEPTED by the Lean checker** ($POL of \`$PID\`). Merged and credited now. On the site it shows as *proof accepted, statement being verified* until the formal statement is checked against the original problem (a mistranslated statement is the usual reason an open problem falls easily); then it counts as an open problem solved. [Run]($RUN_URL)"
    else
      MSG="**ACCEPTED** ($POL of \`$PID\`): ${REASON:-the Lean kernel accepted it and its axioms passed the audit}. Merged and credited. [Run]($RUN_URL)"
    fi
    if jq -e '.labels | map(.name) | index("needs-human-review")' pr.json >/dev/null; then
      gh api -X DELETE "repos/$REPO/issues/$PR/labels/needs-human-review" >/dev/null 2>&1 || true
    fi
    {
      if [ "${REMERGE:-0}" = 0 ]; then comment "$MSG"; fi   # a merge retry does not repeat the verdict
      # Many verdicts merge at once: GitHub refuses a merge when main moved a moment before ("Base branch
      # was modified"). That is a race, not a rejection: retry with a random pause, a few times.
      MERGED=0
      # GitHub never merges a draft: an accepted draft is marked ready first.
      if [ "$(jq -r .draft pr.json)" = "true" ]; then
        gh pr ready "$PR" --repo "$REPO" || true
      fi
      for TRY in 1 2 3 4 5 6 7 8; do
                # REST first (its answer carries the merge commit and it spares the small GraphQL budget); when it answers
        # "Resource not accessible by integration", as it does for many of these pull requests, gh pr merge (GraphQL).
        if OUT="$(gh api -X PUT "repos/$REPO/pulls/$PR/merge" -f merge_method=squash -f sha="$HEAD_SHA" 2>&1)"; then
          MERGED=1; MERGE_SHA="$(printf '%s' "$OUT" | jq -r '.sha // empty' 2>/dev/null || true)"; break
        elif printf '%s' "$OUT" | grep -q "not accessible by integration" && OUT="$(gh pr merge "$PR" --repo "$REPO" --squash --match-head-commit "$HEAD_SHA" 2>&1)"; then
          # the squash commit's sha from git (no API call; the REST answer can lag behind a GraphQL merge)
          MERGE_SHA="$(git -C base fetch -q --depth 100 origin main 2>/dev/null && git -C base log -100 --format='%H %s' FETCH_HEAD | grep -m1 -E " \(#$PR\)\$" | cut -d' ' -f1 || true)"
          MERGED=1; break
        fi
        echo "merge attempt $TRY: $OUT"
        echo "$OUT" | grep -qiE "base branch was modified|try the merge again|is not mergeable|still a draft|timeout|502|503" || break
        sleep $(( (RANDOM % 20) + 5 * TRY ))
      done
      if [ "$MERGED" = 1 ]; then
        # A merge made with GITHUB_TOKEN triggers no other workflow, so credit it here.
        CREDIT_FILES=files.json CREDIT_PR=pr.json MERGE_SHA="${MERGE_SHA:-}" bash base/tools/credit.sh "$PR" || true
      elif [ "$MODE" = new ] && gh api "repos/$REPO/contents/$FPATH?ref=main" >/dev/null 2>&1; then
        comment "Not merged: \`$FPATH\` is already on main (someone else's proof was merged first)."
      elif [ "${REMERGE:-0}" -lt 6 ]; then
        # a refused merge is retried by the merger a few minutes later (the check itself is not re-run)
        touch remerge.flag
        if [ "${REMERGE:-0}" = 0 ]; then comment "Accepted. GitHub refused the merge for now (${OUT:0:160}); the merge is retried automatically in a few minutes, nothing for you to do."; fi
      else
        comment "Accepted, but GitHub kept refusing the merge (${OUT:0:200}). A maintainer will merge it; nothing for you to do."
      fi
    } ;;
  rejected) comment "**REJECTED**: $REASON. Push a fixed file to this pull request, or move on. [Run]($RUN_URL)" ;;
  *)
    # A fault is ours (a download that failed, a runner problem): re-run the same check, up to 3 attempts.
    if [ "${RUN_ATTEMPT:-1}" -lt 3 ] && gh api -X POST "repos/$REPO/actions/runs/$RUN_ID/rerun" >/dev/null; then
      touch rerun.flag
      comment "**FAULT** (our side, not your proof): $REASON. Re-running the check automatically (attempt $((RUN_ATTEMPT + 1)) of 3). [Run]($RUN_URL)"
    else
      comment "**FAULT** (our side, not your proof): $REASON. Three attempts failed; a maintainer has been notified. Pushing any new commit also re-runs the check. [Run]($RUN_URL)"
    fi ;;
esac
