#!/usr/bin/env bash
# One pass over the pull requests that waited under the old human-review rule (label needs-human-review): merge those
# whose latest check of their exact head commit was accepted, after re-running the linter from main; remove the label
# where that check rejected the commit. Covers every labelled pull request (all pages), LANES at a time, each lane in its
# own copy of main. Needs: GH_TOKEN REPO [OMA_SITE] [LANES]; the current directory holds base/ (main).
set -uo pipefail
# The merger (backlog.yml, tools/merger_loop.sh v2) is the only caller now; an older merger still running from before
# tools/merger.v2 existed must not report twice, so it does nothing here.
if [ -e base/tools/merger.v2 ] && [ -z "${MERGER_V2:-}" ]; then exit 0; fi
if [ -e base/tools/merger.v3 ] && [ -z "${MERGER_V3:-}" ]; then exit 0; fi   # the v3 merger has taken over
LANES=${LANES:-3}
gh api --paginate "repos/$REPO/issues?state=open&labels=needs-human-review&per_page=100&sort=created&direction=asc" \
  --jq '.[] | select(.pull_request) | .number' > all.txt || true
# shared API budget: stop before it runs low (the verdicts of new proofs come first)
MINB=${BACKLOG_MIN_BUDGET:-0}
# Proofs whose statement was already checked (content/open_review.json: confirmed first, then the others) go first:
# a confirmed proof of an open problem counts on the site only once it is merged.
python3 -I - all.txt base/content/open_review.json <<'PY2' || true
import json, sys
nums = [l.strip() for l in open(sys.argv[1]) if l.strip()]
try:
    rv = json.load(open(sys.argv[2]))
except Exception:
    rv = {}
first = [str(v.get("pr")) for sec in ("confirmed", "known", "flagged") for v in rv.get(sec, {}).values() if v.get("pr")]
order = list(dict.fromkeys([n for n in first if n in set(nums)] + nums))
open(sys.argv[1], "w").write("".join(n + "\n" for n in order))
PY2
echo "$(wc -l < all.txt) pull requests in this batch"
lane() {  # $1 = lane number; works in lane_$1/ with its own base/ copy and prs.txt
  cd "lane_$1" || return
  N=0
  while read -r PR; do
    if [ "$MINB" -gt 0 ] && [ $((N % 10)) = 0 ]; then
      R0=$(gh api rate_limit --jq .resources.core.remaining 2>/dev/null || echo 9999)
      [ "$R0" -lt "$MINB" ] && { echo "budget low ($R0 left): stopping this pass"; break; }
    fi
  N=$((N+1))
  gh api "repos/$REPO/pulls/$PR" > pr.json || continue
  # merged or closed meanwhile (by a verdict or another lane): nothing to do
  [ "$(jq -r .state pr.json)" = open ] || continue
  jq -e '.labels | map(.name) | index("needs-human-review")' pr.json >/dev/null || continue
  SHA=$(jq -r .head.sha pr.json)
  gh api "repos/$REPO/pulls/$PR/files" > files.json || continue
  if [ "$(jq 'length' files.json)" != 1 ] || [ "$(jq -r '.[0].status' files.json)" != added ]; then echo "#$PR: not a single new file, left for a person"; continue; fi
  FPATH=$(jq -r '.[0].filename' files.json)
  echo "$FPATH" | grep -qE '^(proofs|reductions|statements)/[A-Za-z0-9_.'"'"'-]+\.lean$' || { echo "#$PR: unexpected path"; continue; }
  # the latest completed check of this exact commit
  RUN=$(gh api "repos/$REPO/actions/runs?head_sha=$SHA&event=pull_request&status=completed&per_page=20" \
        --jq '[.workflow_runs[] | select(.name=="check-proof")] | sort_by(.created_at) | last | .id // empty')
  [ -n "$RUN" ] || { echo "#$PR: no completed check for $SHA"; continue; }
  rm -rf art; gh run download "$RUN" --repo "$REPO" -n verdict -D art >/dev/null 2>&1 || { echo "#$PR: no verdict artifact"; continue; }
  V=$(jq -r .verdict art/verdict.json)
  if [ "$V" = rejected ]; then
    # the latest check of this commit refused it (the author was told so in the check's comment): not waiting for anyone
    gh pr edit "$PR" --repo "$REPO" --remove-label needs-human-review >/dev/null 2>&1; echo "#$PR: latest check rejected, label removed"; continue
  fi
  [ "$V" = accepted ] || { echo "#$PR: check verdict is $V"; continue; }
  if gh api "repos/$REPO/contents/$FPATH?ref=main" >/dev/null 2>&1; then
    gh pr comment "$PR" --repo "$REPO" --body "Closing: \`$FPATH\` is already on main (another proof of the same target was merged first). Thank you; take the next problem." >/dev/null
    gh pr close "$PR" --repo "$REPO" >/dev/null; gh pr edit "$PR" --repo "$REPO" --remove-label needs-human-review >/dev/null 2>&1
    continue
  fi
  # the linter from main, on the exact file of the checked commit
  mkdir -p "base/$(dirname "$FPATH")"
  gh api "repos/$REPO/contents/$FPATH?ref=$SHA" --jq .content | base64 -d > "base/$FPATH" || continue
  if ! (cd base && python3 -I tools/lint.py "$FPATH" data/catalog.json > "${RELINT:-/tmp/relint.json}"); then
    echo "#$PR: trusted lint refused: $(jq -c .errors "${RELINT:-/tmp/relint.json}")"; rm -f "base/$FPATH"; continue
  fi
  rm -f "base/$FPATH"
  KIND=$(python3 -I -c 'import json,os;d=json.load(open(os.environ.get("RELINT","/tmp/relint.json")));print(d["type"] if d["type"] in ("reduction","statement") else d["kind"])')
  if [ "$KIND" = open ]; then
    MSG="**Merged.** The Lean checker had accepted this proof; it waited for a review under an old rule, now replaced. It is credited to you now. On the site it shows as *proof accepted, statement being verified* until the formal statement is checked against the original problem; then it counts as an open problem solved."
  elif [ "$KIND" = statement ]; then
    MSG="**Merged.** The statement compiled; it waited for a review under an old rule, now replaced. The problem is provable by everyone now and the formalization is credited to you. Its faithfulness to the source is checked separately."
  else
    MSG="**Merged.** The Lean checker had accepted this; it waited for a review under an old rule, now replaced. Credited to you now."
  fi
  [ "$(jq -r .draft pr.json)" = true ] && gh pr ready "$PR" --repo "$REPO" >/dev/null 2>&1
  MERGED=0
  for TRY in 1 2 3 4 5; do
    if OUT="$(gh pr merge "$PR" --repo "$REPO" --squash --match-head-commit "$SHA" 2>&1)"; then MERGED=1; break; fi
    echo "#$PR merge attempt $TRY: ${OUT:0:160}"
    echo "$OUT" | grep -qiE "base branch was modified|try the merge again|is not mergeable|timeout|502|503" || break
    sleep $((3 * TRY))
  done
  if [ "$MERGED" = 1 ]; then
    gh pr comment "$PR" --repo "$REPO" --body "$MSG" >/dev/null
    gh pr edit "$PR" --repo "$REPO" --remove-label needs-human-review >/dev/null 2>&1
    CREDIT_FILES=files.json bash base/tools/credit.sh "$PR" >/dev/null 2>&1 || echo "#$PR: credit will be retried by the site"
    echo "#$PR: merged ($KIND)"
  fi
  done < prs.txt
  echo "done: $N looked at (lane $1)"
}
PIDS=()
trap 'kill "${PIDS[@]}" 2>/dev/null' TERM INT
for L in $(seq 0 $((LANES - 1))); do
  rm -rf "lane_$L"; mkdir -p "lane_$L"; cp -a "$(readlink -f base)" "lane_$L/base"
  awk -v n="$LANES" -v l="$L" 'NR % n == l' all.txt > "lane_$L/prs.txt"
  RELINT="$PWD/lane_$L/relint.json" lane "$L" &
  PIDS+=($!)
done
wait
