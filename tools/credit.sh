#!/usr/bin/env bash
# Tells the site that pull request $1 was merged. Run only by the trusted verdict workflow (never on PR code).
# It reads the pull request with the workflow's own GitHub token and sends it with an OIDC token that proves to the
# site where the request comes from, so the site needs no GitHub API call of its own (anonymous calls are rate-limited).
set -euo pipefail
PR="$1"
SITE="${OMA_SITE:-https://lefttosolve.com}"
# The caller may pass the pull request it already read (CREDIT_PR) and the merge commit it just made (MERGE_SHA):
# then no API call is needed here (the GitHub API budget is shared by every job of the repository).
if [ -n "${CREDIT_PR:-}" ] && [ -s "${CREDIT_PR}" ] && [ -n "${MERGE_SHA:-}" ]; then
  pr=$(jq --arg sha "$MERGE_SHA" '.merged = true | .merge_commit_sha = $sha' "$CREDIT_PR")
else
  # right after a merge through GraphQL (gh pr merge) the REST API can still say merged=false for a few seconds, and
  # the site then refuses the credit (not_merged): wait for GitHub to agree, then send
  for TRY in 1 2 3; do
    pr=$(gh api "repos/$REPO/pulls/$PR") || pr=""
    [ "$(printf '%s' "$pr" | jq -r '.merged // false' 2>/dev/null)" = true ] && break
    sleep 4
  done
  [ -n "$pr" ] || { echo "$PR" >> "${CREDIT_RETRY_FILE:-/dev/null}"; exit 1; }
fi
# the caller may pass the file list it already fetched for this same pull request (saves an API call)
if [ -n "${CREDIT_FILES:-}" ] && [ -s "${CREDIT_FILES}" ]; then files=$(cat "$CREDIT_FILES"); else files=$(gh api "repos/$REPO/pulls/$PR/files"); fi
oidc=""
if [ -n "${ACTIONS_ID_TOKEN_REQUEST_URL:-}" ]; then
  oidc=$(curl -sS -m 30 -H "Authorization: bearer $ACTIONS_ID_TOKEN_REQUEST_TOKEN" "$ACTIONS_ID_TOKEN_REQUEST_URL&audience=lefttosolve.com" | jq -r '.value // ""')
fi
jq -n --argjson pr "$pr" --argjson files "$files" --arg oidc "$oidc" '{
  pr: $pr.number, oidc: $oidc, merged: $pr.merged, base: $pr.base.ref, handle: $pr.user.login, body: ($pr.body // ""),
  mergeSha: $pr.merge_commit_sha, url: $pr.html_url, files: [$files[] | {filename, status}]
}' > credit.json
# The site answers {"ok":true} when the credit is recorded. A transient error (GitHub or database busy, merge not seen
# yet) is retried here, then handed to the merger (CREDIT_RETRY_FILE), which retries it every 10 minutes; a refusal
# for a reason that will not change (unknown problem, bad reduction) is final.
# One try of at most 15 s: a slow or failing site must never hold a verdict slot of the merger; the merger retries
# failures later in the background.
for TRY in 1; do
  OUT=$(curl -sS -m 15 -X POST "$SITE/api/verdict" -H "Content-Type: application/json" --data @credit.json 2>&1 || true)
  echo "$OUT"
  printf '%s' "$OUT" | grep -q '"ok":true' && exit 0
  printf '%s' "$OUT" | grep -qE '"error":"(unknown_problem|unknown_step|unknown_target|bad_reduction|too_many_reductions|not_a_single_new_file|not_a_proof|not_formalized_yet|hyps_out_of_range|bad_request)"' && exit 0
done
echo "$PR" >> "${CREDIT_RETRY_FILE:-/dev/null}"
exit 1
