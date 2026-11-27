#!/usr/bin/env bash
# The merger: one long-running trusted job that gives every finished check-proof run its verdict (tools/verdict_one.sh)
# and runs the backlog pass (tools/backlog_pass.sh) when the API budget allows. One runner slot instead of one queued
# verdict job per proof. Never checks out or runs pull request code.
# GitHub's API budget for GITHUB_TOKEN is shared by every job of the repository, so polling is kept cheap: the runs
# in progress are listed every loop (1-2 calls) and a run that leaves that list is read once; a full scan of the last
# three hours runs every 10 minutes, in 30-minute slices (GitHub returns at most 1,000 runs per query: a single query
# over hours silently dropped the oldest runs, whose proofs then waited for hours without a verdict).
# v3: a green check run means accepted and its title carries the PR number, so accepted runs need no artifact
# download; the loop also restarts itself on a new version of this script pushed to main (state kept in done/).
# v4: verdicts go oldest pull request first (the filing order decides who solves a problem first), at most $BATCH per
# loop so polling never pauses for long; runs listed in base/tools/requeue.tsv (lost by earlier versions) are given
# their verdict once; an accepted run whose merge was refused is retried even after a restart; credits that the site
# did not record are retried every 10 minutes.
# Needs: GH_TOKEN REPO [OMA_SITE]; base/ (a checkout of main) in the current directory.
set -uo pipefail
export MERGER_V2=1 MERGER_V3=1
# Every GitHub call has a time limit: one call that never answers must not stall all verdicts.
GH_BIN="$(type -P gh)"; export GH_BIN
gh() { timeout 90 "$GH_BIN" "$@"; }
export -f gh
ROOT="$PWD"; mkdir -p "$ROOT/done" "$ROOT/remerge"
export CREDIT_RETRY_FILE="$ROOT/credit_retry.txt"; touch "$CREDIT_RETRY_FILE"
SELF="$ROOT/base/tools/merger_loop.sh"; SELF_SHA=$(sha1sum "$SELF" | cut -d' ' -f1)
# Hand-over without a gap: a job lasts at most 6 hours and a new one waits in GitHub's runner queue (behind hundreds of
# proof checks) before it starts, so the next merger is started early (every 20 minutes, no concurrency group) and
# waits on standby until the running merger ends. A job that finds a merger with more than 75 minutes left, or another
# standby, stops at once (a few seconds of a runner).
INITIAL_BACK=10800
if [ -z "${MERGER_RESUME:-}" ] && [ -n "${GITHUB_RUN_ID:-}" ]; then
  TOOK_OVER=0
  while :; do
    gh api "repos/$REPO/actions/workflows/backlog.yml/runs?status=in_progress&per_page=30" \
      --jq '.workflow_runs[] | [.id, (.run_started_at // .created_at)] | @tsv' > mergers.tsv 2>/dev/null || { sleep 30; continue; }
    MINE=$(awk -F'\t' -v me="$GITHUB_RUN_ID" '$1 == me {print $2}' mergers.tsv); MINE=${MINE:-$(date -u +%FT%TZ)}
    OLDEST=$(awk -F'\t' -v me="$GITHUB_RUN_ID" '$1 != me' mergers.tsv | sort -t$'\t' -k2 | head -n 1)
    [ -n "$OLDEST" ] || break                                   # no other merger: this one works
    OSTART=$(printf '%s' "$OLDEST" | cut -f2)
    [[ "$OSTART" > "$MINE" ]] && break                          # the others started after this one: this one works
    LEFT=$(( $(date -u -d "$OSTART" +%s) + ${MERGER_SECONDS:-20400} + 300 - $(date -u +%s) ))
    OTHERS=$(awk -F'\t' -v me="$GITHUB_RUN_ID" -v o="$OSTART" -v m="$MINE" '$1 != me && $2 > o && $2 < m' mergers.tsv | wc -l)
    if [ "$OTHERS" -gt 0 ] || [ "$LEFT" -gt 4500 ]; then
      echo "merger: another merger is running (${LEFT}s left, $OTHERS on standby): nothing to do"; exit 0
    fi
    echo "merger: standby, the running merger ends in about ${LEFT}s"; TOOK_OVER=1; sleep 60
  done
  # taking over from a merger that just ended: it handled everything but the last minutes
  [ "$TOOK_OVER" = 1 ] && INITIAL_BACK=2400
fi
if [ -n "${MERGER_RESUME:-}" ]; then
  # restarted by an older version of this loop after an update: same job, same deadline, same state
  START=$MERGER_START; END=$MERGER_END; BPID=${MERGER_BPID:-}; LAST_BACKLOG=${MERGER_LAST_BACKLOG:-0}; LAST_SCAN=0
  INITIAL_BACK=${MERGER_INITIAL_BACK:-10800}
  touch "$ROOT/watch.txt" "$ROOT/prev_inprog.tsv"
  echo "merger: resumed on version $SELF_SHA"
else
  : > "$ROOT/watch.txt"; : > "$ROOT/prev_inprog.tsv"
  START=$(date -u +%s); END=$(( START + ${MERGER_SECONDS:-20400} ))   # 5 h 40 min, under the 6 h job limit
  BPID=""; LAST_BACKLOG=0; LAST_SCAN=0
fi
touch "$ROOT/queue.tsv"
SLOTS=${SLOTS:-4}; BATCH=${BATCH:-40}; declare -A SPID; LAST_REFRESH=0; LAST_OLD=0; OLDJOBS=1; LAST_CREDIT=0; REQ_SHA=""; LAST_PENDING=0; CPID=""
iso() { date -u -d "@$1" +%Y-%m-%dT%H:%M:%SZ; }
JQ_RUN='[.id, .head_sha, .run_attempt, .html_url, .updated_at, (.conclusion // ""), (.display_title // "")] | @tsv'
remaining() { gh api rate_limit --jq '"\(.resources.core.remaining) \(.resources.core.reset)"' 2>/dev/null || echo "999 0"; }
budget() {  # never let the repository run dry: other jobs (checks, deploys) need the API too; GraphQL is checked too
  local rem reset grem greset; read -r rem reset grem greset < <(gh api rate_limit --jq '"\(.resources.core.remaining) \(.resources.core.reset) \(.resources.graphql.remaining) \(.resources.graphql.reset)"' 2>/dev/null || echo "999 0 999 0")
  echo "budget: core $rem, graphql $grem, queue $(wc -l < "$ROOT/queue.tsv")"
  if [ "${rem:-999}" -lt 300 ]; then echo "API budget low ($rem left), waiting for the reset"; sleep $(( reset - $(date -u +%s) + 5 )); fi
  if [ "${grem:-999}" -lt 60 ]; then echo "GraphQL budget low ($grem left), waiting for the reset"; sleep $(( greset - $(date -u +%s) + 5 )); fi
}
refresh() {  # main moved on (merges): pull it and sync each verdict slot's copy (rsync: only what changed)
  git -C "$ROOT/base" fetch -q --depth 1 origin main && git -C "$ROOT/base" reset -q --hard FETCH_HEAD; git -C "$ROOT/base" clean -fdq
  for d in $(seq 1 "$SLOTS"); do
    if command -v rsync >/dev/null; then rsync -a --delete "$ROOT/base/" "$ROOT/base_$d/"; else rm -rf "$ROOT/base_$d"; cp -a "$ROOT/base" "$ROOT/base_$d"; fi
  done
}
scan() {  # completed runs created in the last $1 seconds, in 30-minute slices (at most 1,000 runs per query)
  local NOW A B FLOOR; NOW=$(date -u +%s); FLOOR=$(( START - INITIAL_BACK ))
  A=$(( NOW - $1 )); [ "$A" -lt "$FLOOR" ] && A=$FLOOR      # never before what this merger is responsible for
  for (( ; A < NOW; A += 1800 )); do
    B=$(( A + 1800 ))
    gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=completed&per_page=100&created=$(iso $A)..$(iso $B)" \
      --jq ".workflow_runs[] | select(.conclusion != \"cancelled\") | $JQ_RUN" 2>/dev/null || true
  done
}
publish_pending() {  # the open pull requests, by problem id (their title), to the site: the desk stops handing them out
  # only those opened in the last 12 hours and not rejected by this merger: an abandoned or rejected pull request must
  # not keep a problem away from everyone
  local CUT; CUT=$(iso $(( $(date -u +%s) - 43200 )))
  gh api --paginate "repos/$REPO/pulls?state=open&per_page=100" \
    --jq ".[] | select(.created_at > \"$CUT\")" 2>/dev/null | jq -c --slurpfile rej <(sort -un "$ROOT/rejected.txt" 2>/dev/null | jq -s '.') \
    'select((.number as $n | $rej[0] | index($n)) | not) | {id: (.title | sub("^(proof|disproof|statement|reduction|reduce|step|formalize|Proof)\\s*:\\s*"; "") | gsub("^\\s+|\\s+$"; "")), pr: .number, since: .created_at}' \
    2>/dev/null | jq -s '.' > open_prs.json || return 0
  [ -s open_prs.json ] || return 0
  local OIDC=""
  if [ -n "${ACTIONS_ID_TOKEN_REQUEST_URL:-}" ]; then
    OIDC=$(curl -sS -m 30 -H "Authorization: bearer $ACTIONS_ID_TOKEN_REQUEST_TOKEN" "$ACTIONS_ID_TOKEN_REQUEST_URL&audience=lefttosolve.com" | jq -r '.value // ""')
  fi
  jq -n --slurpfile items open_prs.json --arg oidc "$OIDC" '{oidc: $oidc, items: $items[0]}' > pending_post.json
  echo "merger: pending list $(jq length open_prs.json) open pull requests: $(curl -sS -m 60 -X POST "${OMA_SITE:-https://lefttosolve.com}/api/pending" -H 'Content-Type: application/json' --data @pending_post.json 2>&1 | head -c 120)"
}
verdict() {  # $1 run id, $2 head sha, $3 attempt, $4 url, $5 old (1/0), $6 slot, $7 conclusion, $8 title, $9 mode
  local ID="$1" SHA="$2" ATT="$3" URL="$4" OLD="$5" B="$ROOT/base_$6" W="$ROOT/work_$6" CONC="$7" TITLE="$8" MODE="${9:-}" PR
  rm -rf "$W"; mkdir -p "$W"; ln -s "$B" "$W/base"
  if [ "$CONC" = success ] && [[ "$TITLE" =~ ^check-proof\ \#([0-9]+)$ ]]; then
    # green = accepted (check-proof fails every other verdict); kind and polarity come from the trusted re-lint
    mkdir -p "$W/artifact"; echo "${BASH_REMATCH[1]}" > "$W/artifact/pr.txt"; echo '{"verdict":"accepted","reason":""}' > "$W/artifact/verdict.json"
  elif ! gh run download "$ID" --repo "$REPO" -n verdict -D "$W/artifact" >/dev/null 2>&1; then
    # not finished yet (left the in-progress list for a re-run or a queue) or no artifact: look again later
    echo "$ID" >> "$ROOT/watch.txt"; rm -f "$ROOT/done/$ID.$ATT"; return 0
  fi
  PR=$(head -c 12 "$W/artifact/pr.txt" 2>/dev/null | tr -cd '0-9'); [ -n "$PR" ] || return 0
  local RM; RM=$(cat "$ROOT/remerge/$PR" 2>/dev/null || echo 0)
  [ "$MODE" = remerge ] && [ "$RM" = 0 ] && RM=1               # requeued: accepted and reported before, merge again
  if [ "$OLD" = 1 ] && gh api "repos/$REPO/issues/$PR/comments?per_page=100" --jq '.[].body' 2>/dev/null | grep -qF "$URL"; then
    # already reported (by an earlier merger): a rejection stays reported; an accepted proof still open was not merged
    # (a refused merge whose retries were lost in a restart): merge it now without repeating the verdict
    [ "$CONC" = success ] || return 0
    [ "$RM" = 0 ] && RM=1
  fi
  ( cd "$W" && RELINT="$W/relint.json" RUN_ID="$ID" RUN_ATTEMPT="$ATT" HEAD_SHA="$SHA" RUN_URL="$URL" REMERGE="$RM" \
      timeout 900 bash "$B/tools/verdict_one.sh" ) > "$W/log.txt" 2>&1
  echo "#$PR run $ID.$ATT: exit $? $(grep -m1 -oiE 'rate limit|ACCEPTED|REJECTED|FAULT|already on main' "$W/log.txt" || true)"
  grep -qE 'REJECTED|already on main' "$W/log.txt" && echo "$PR" >> "$ROOT/rejected.txt"
  [ -e "$W/rerun.flag" ] && echo "$ID" >> "$ROOT/watch.txt"   # a fault re-runs the check: same run id, next attempt
  if [ -e "$W/remerge.flag" ]; then                               # merge refused: try the same verdict again later
    echo $((RM + 1)) > "$ROOT/remerge/$PR"; rm -f "$ROOT/done/$ID.$ATT"; echo "$ID" >> "$ROOT/watch.txt"
  fi
  git -C "$B" clean -fdq -- proofs reductions statements 2>/dev/null || true
}
refresh
while [ "$(date -u +%s)" -lt "$END" ]; do
  NOW=$(date -u +%s); budget
  : > cand.tsv
  # 1. runs that were in progress at the last poll and are not any more
  gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=in_progress&per_page=100" --jq ".workflow_runs[] | $JQ_RUN" > inprog.tsv 2>/dev/null || cp prev_inprog.tsv inprog.tsv
  cut -f1 inprog.tsv | sort > now_ids; cut -f1 prev_inprog.tsv | sort > prev_ids
  comm -23 prev_ids now_ids > left_ids
  for LID in $(cat left_ids); do
    gh api "repos/$REPO/actions/runs/$LID" --jq "select(.status == \"completed\" and .conclusion != \"cancelled\") | $JQ_RUN" >> cand.tsv 2>/dev/null \
      || echo "$LID" >> watch.txt
  done
  mv inprog.tsv prev_inprog.tsv
  # 2. every 10 minutes (and at start): a full scan of runs created in the last three hours, in slices
  if [ $(( NOW - LAST_SCAN )) -ge 600 ]; then LAST_SCAN=$NOW; scan 10800 >> cand.tsv; fi
  # 3. re-runs and runs that were not finished when first seen
  for WID in $(sort -u watch.txt); do
    gh api "repos/$REPO/actions/runs/$WID" --jq "select(.status == \"completed\" and .conclusion != \"cancelled\") | $JQ_RUN" >> cand.tsv 2>/dev/null || true
  done
  : > watch.txt
  # verdict jobs queued by the old per-proof trigger still run: leave their commits to them (no double report)
  if [ "$OLDJOBS" = 1 ] && [ $(( NOW - LAST_OLD )) -ge 300 ]; then
    LAST_OLD=$NOW; : > pending.txt
    gh api --paginate "repos/$REPO/actions/workflows/verdict.yml/runs?status=queued&per_page=100" \
      --jq '.workflow_runs[] | select(.event == "workflow_run") | .head_sha' >> pending.txt 2>/dev/null || echo x >> pending.txt
    [ -s pending.txt ] || OLDJOBS=0
  fi
  if [ $(( NOW - LAST_REFRESH )) -ge 120 ]; then
    LAST_REFRESH=$NOW; refresh
    if [ "$(sha1sum "$SELF" | cut -d' ' -f1)" != "$SELF_SHA" ]; then
      echo "merger: new version on main, restarting in place"
      export MERGER_RESUME=1 MERGER_START=$START MERGER_END=$END MERGER_BPID=$BPID MERGER_LAST_BACKLOG=$LAST_BACKLOG MERGER_INITIAL_BACK=$INITIAL_BACK
      exec bash "$SELF"
    fi
  fi
  # 4. runs that earlier versions lost (base/tools/requeue.tsv, same columns plus a mode): queued once per version of it
  if [ -s base/tools/requeue.tsv ] && [ "$(sha1sum base/tools/requeue.tsv | cut -d' ' -f1)" != "$REQ_SHA" ]; then
    REQ_SHA=$(sha1sum base/tools/requeue.tsv | cut -d' ' -f1); grep -v '^#' base/tools/requeue.tsv >> cand.tsv
    echo "merger: requeued $(grep -vc '^#' base/tools/requeue.tsv) runs"
  fi
  # 5. the queue: new candidates join what is left from earlier loops; oldest pull request first; at most BATCH now
  cat queue.tsv cand.tsv | awk -F'\t' 'NF >= 6 && !seen[$1]++' > all.tsv
  : > next.tsv
  while IFS=$'\t' read -r ID SHA ATT URL UPD CONC TITLE MODE; do
    [ -n "$ID" ] || continue
    [ -n "$CONC" ] || { echo "$ID" >> watch.txt; continue; }   # not finished yet
    [ -e "done/$ID.$ATT" ] && continue
    [ "$OLDJOBS" = 1 ] && grep -qx "$SHA" pending.txt 2>/dev/null && { touch "done/$ID.$ATT"; continue; }   # an old verdict job reports it
    N=$(printf '%s' "$TITLE" | grep -oE '[0-9]+$' || echo 999999)
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$ID" "$SHA" "$ATT" "$URL" "$UPD" "$CONC" "$TITLE" "${MODE:-}" >> next.tsv
  done < all.tsv
  sort -t$'\t' -k1,1n -k2,2n next.tsv | cut -f2- > sorted.tsv
  head -n "$BATCH" sorted.tsv > batch.tsv; tail -n +"$(( BATCH + 1 ))" sorted.tsv > queue.tsv
  while IFS=$'\t' read -r ID SHA ATT URL UPD CONC TITLE MODE; do
    touch "done/$ID.$ATT"
    OLD=0; [ "$(date -u -d "$UPD" +%s 2>/dev/null || echo 0)" -lt "$START" ] && OLD=1
    [ -n "${MODE:-}" ] && OLD=0   # requeued runs: checked by hand to have no verdict (or a refused merge)
    while :; do
      FREE=""; for i in $(seq 1 "$SLOTS"); do { [ -z "${SPID[$i]:-}" ] || ! kill -0 "${SPID[$i]}" 2>/dev/null; } && { FREE=$i; break; }; done
      [ -n "$FREE" ] && break; sleep 1
    done
    verdict "$ID" "$SHA" "$ATT" "$URL" "$OLD" "$FREE" "$CONC" "$TITLE" "${MODE:-}" & SPID[$FREE]=$!
  done < batch.tsv
  for i in $(seq 1 "$SLOTS"); do [ -n "${SPID[$i]:-}" ] && wait "${SPID[$i]}" 2>/dev/null; SPID[$i]=""; done
  # 6. credits the site did not record (it answered an error): retry every 10 minutes
  # in the background and at most 5 minutes per pass, never blocking the verdicts (the site may be down for hours)
  if [ -s "$CREDIT_RETRY_FILE" ] && [ $(( NOW - LAST_CREDIT )) -ge 600 ] && { [ -z "${CPID:-}" ] || ! kill -0 "$CPID" 2>/dev/null; }; then
    LAST_CREDIT=$NOW; sort -u "$CREDIT_RETRY_FILE" > credit_all.txt; head -n 30 credit_all.txt > credit_todo.txt
    tail -n +31 credit_all.txt > "$CREDIT_RETRY_FILE"
    ( C="$ROOT/credit_work"; rm -rf "$C"; mkdir -p "$C"; cd "$C"
      timeout 300 bash -c 'for P in $(cat "$1"); do bash "$2/tools/credit.sh" "$P" >/dev/null 2>&1 || true; done' _ "$ROOT/credit_todo.txt" "$ROOT/base" || true
      echo "merger: retried $(wc -l < "$ROOT/credit_todo.txt") credits in the background" ) &
    CPID=$!
  fi
  # 7. every 15 minutes: the open pull requests to the site, so no agent is sent to a problem with a proof waiting
  if [ $(( NOW - LAST_PENDING )) -ge 900 ]; then LAST_PENDING=$NOW; publish_pending; fi
  # backlog: only when no pass is running, at most every 15 minutes, and with budget to spare for the verdicts
  read -r REM _ < <(remaining)
  if { [ -z "$BPID" ] || ! kill -0 "$BPID" 2>/dev/null; } && [ $(( NOW - LAST_BACKLOG )) -ge 900 ] && [ "${REM:-0}" -gt 1500 ] && [ ! -s queue.tsv ]; then
    LAST_BACKLOG=$NOW; B="$ROOT/backlog"; rm -rf "$B"; mkdir -p "$B"; cp -a "$ROOT/base" "$B/base"
    ( cd "$B" && LANES=1 BACKLOG_MIN_BUDGET=800 timeout 3000 bash "$B/base/tools/backlog_pass.sh" 2>&1 | grep -E "merged|batch|done:|budget" | sed 's/^/backlog: /' ) &
    BPID=$!
  fi
  [ -s queue.tsv ] || sleep 30
done
wait
echo "merger: time is up; the next scheduled run takes over"
