#!/usr/bin/env bash
# End-to-end tests of tools/oma.sh against a mock site, a fake gh and a local bare git remote.
# No network, no Lean: the checker is replaced by a stub through OMA_CHECK. Run: bash tests/test_oma.sh
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
T="$(mktemp -d)"
PORT=$((20000 + RANDOM % 20000))
export MOCK_LOG="$T/requests.log"; : > "$MOCK_LOG"
python3 -I "$ROOT/tests/mock_desk.py" "$PORT" & MOCK=$!
trap 'kill $MOCK 2>/dev/null; rm -rf "$T"' EXIT
FAILS=0
pass() { echo "PASS $1"; }
fail() { echo "FAIL $1"; FAILS=$((FAILS+1)); }
check() { if eval "$2"; then pass "$1"; else fail "$1"; fi; }

# A working copy of the repository with a bare "origin" (the agent's fork) and a fake gh.
git init -q --bare "$T/origin.git"
git clone -q "$T/origin.git" "$T/repo" 2>/dev/null
cp -r "$ROOT/tools" "$ROOT/data" "$T/repo/" ; mkdir -p "$T/repo/proofs"; touch "$T/repo/proofs/.keep"
cd "$T/repo" && git add -A && git -c user.name=t -c user.email=t@t commit -qm init && git push -q origin HEAD:main 2>/dev/null
git remote set-head origin main 2>/dev/null || git symbolic-ref refs/remotes/origin/HEAD refs/remotes/origin/main
mkdir -p "$T/bin"
cat > "$T/bin/gh" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = "api" ] && [ "$2" = "user" ]; then echo tester; exit 0; fi
if [ "$1" = "pr" ] && [ "$2" = "create" ]; then printf '%s\n' "$@" > "$GH_LOG"; echo "https://github.com/x/y/pull/1"; exit 0; fi
exit 1
EOF
cat > "$T/bin/stubcheck" <<'EOF'
#!/usr/bin/env bash
# stub checker: accepted unless the file contains the word REJECTME
if grep -q REJECTME "$1"; then echo '{"verdict":"rejected","reason":"stub says no","log":"x"}' > "$2"; exit 1; fi
echo '{"verdict":"accepted","reason":"stub ok","log":""}' > "$2"
EOF
chmod +x "$T/bin/gh" "$T/bin/stubcheck"
export PATH="$T/bin:$PATH" GH_LOG="$T/gh.log" OMA_SITE="http://127.0.0.1:$PORT" OMA_CHECK="$T/bin/stubcheck" OMA_AGENT=claude-code OMA_MODEL=test-model
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
for i in $(seq 1 30); do curl -s -o /dev/null "http://127.0.0.1:$PORT/api/stats" && break; sleep 0.2; done

PID=Erdos3.erdos_3.variants.gowers
OUT="$(tools/oma.sh next --problem $PID 2>&1)"
check "next: prints the problem" '[[ "$OUT" == *"PROBLEM    $PID"* ]]'
check "next: writes the skeleton" '[ -f "proofs/$PID.lean" ] && grep -q "OMA.solution" "proofs/$PID.lean"'
check "next: prints the role and teammates" '[[ "$OUT" == *"YOUR ROLE   CHECKER: Test the statement."* ]] && [[ "$OUT" == *"TEAMMATES   @mate (lead)"* ]]'
check "next: stores the lease" '[ "$(cat .oma/leases/$PID)" = "22222222-2222-2222-2222-222222222222" ]'
check "next: downloads the brief" 'grep -q "BRIEF FOR $PID" .oma/briefs/$PID.txt'
check "next: sends handle and agent" 'grep -q "\"handle\": \"tester\"" "$MOCK_LOG" && grep -q "\"agent\": \"claude-code\"" "$MOCK_LOG"'
check "next: passes --problem" 'grep -q "\"problem\": \"$PID\"" "$MOCK_LOG"'
OUT="$(tools/oma.sh next --problem nope 2>&1)"; RC=$?
check "next: desk error is reported and fails" '[ $RC -ne 0 ] && [[ "$OUT" == *"not_found"* ]]'
OUT="$(tools/oma.sh next --bogus x 2>&1)"; RC=$?
check "next: unknown option fails" '[ $RC -ne 0 ] && [[ "$OUT" == *"unknown option"* ]]'

OUT="$(tools/oma.sh beat $PID 2>&1)"
check "beat: ok with role and teammates" '[[ "$OUT" == "ok · role checker · teammates: @mate (lead)"* ]]'
check "beat: prints new teammate notes" '[[ "$OUT" == *"NEW NOTE #41 @mate"*"PLAN: induction on k"* ]]'
OUT="$(tools/oma.sh beat $PID 2>&1)"
check "beat: remembers the last note seen (since)" '[[ "$OUT" != *"NEW NOTE"* ]]'
echo 33333333-3333-3333-3333-333333333333 > .oma/leases/stopped; OUT="$(tools/oma.sh beat stopped 2>&1)"; RC=$?
check "beat: STOP on 410 and lease dropped" '[ $RC -eq 3 ] && [[ "$OUT" == STOP* ]] && [ ! -f .oma/leases/stopped ]'
OUT="$(tools/oma.sh beat not-held 2>&1)"; RC=$?
check "beat: refuses a problem without lease" '[ $RC -ne 0 ] && [[ "$OUT" == *"no lease"* ]]'

OUT="$(tools/oma.sh check $PID 2>&1)"; RC=$?
check "check: accepted" '[ $RC -eq 0 ] && [[ "$OUT" == ACCEPTED* ]]'
echo "-- REJECTME" >> "proofs/$PID.lean"; OUT="$(tools/oma.sh check $PID 2>&1)"; RC=$?
check "check: rejected fails" '[ $RC -ne 0 ] && [[ "$OUT" == REJECTED* ]]'
OUT="$(tools/oma.sh submit $PID 2>&1)"; RC=$?
check "submit: refuses when check fails" '[ $RC -ne 0 ] && [ ! -s "$GH_LOG" ]'
sed -i '/REJECTME/d' "proofs/$PID.lean"

echo "unrelated" > stray.txt
OUT="$(tools/oma.sh submit $PID 2>&1)"; RC=$?
check "submit: succeeds" '[ $RC -eq 0 ] && [[ "$OUT" == *"sent"* ]]'
check "submit: PR body has Lease, Agent, Model" 'grep -q "Lease: 22222222" "$GH_LOG" && grep -q "Agent: claude-code" "$GH_LOG" && grep -q "Model: test-model" "$GH_LOG"'
check "submit: PR title is the id" 'grep -qx "$PID" "$GH_LOG"'
BR="oma/$PID"
check "submit: pushed a branch with exactly that file" '[ "$(git --git-dir="$T/origin.git" diff --name-only main "$BR" 2>/dev/null)" = "proofs/$PID.lean" ]'
check "submit: stray files not committed" 'git --git-dir="$T/origin.git" show --name-only --format= "$BR" >/dev/null && ! git --git-dir="$T/origin.git" show --name-only --format= "$BR" | grep -q stray.txt'
check "submit: releases as submitted" 'grep -q "\"reason\": \"submitted\"" "$MOCK_LOG"'
check "submit: lease forgotten" '[ ! -f .oma/leases/$PID ]'

tools/oma.sh next --problem $PID >/dev/null 2>&1
OUT="$(tools/oma.sh reduce $PID 2>&1)"
check "reduce: writes R1" '[ -f "reductions/$PID.R1.lean" ] && grep -q "namespace OMA.R_1" "reductions/$PID.R1.lean"'
OUT="$(tools/oma.sh reduce $PID 2>&1)"
check "reduce: next one is R2" '[ -f "reductions/$PID.R2.lean" ] && grep -q "OMA.R_2" "reductions/$PID.R2.lean"'
rm "reductions/$PID.R2.lean"; : > "$MOCK_LOG"; : > "$GH_LOG"
OUT="$(tools/oma.sh submit $PID.R1 2>&1)"; RC=$?
check "submit reduction: succeeds" '[ $RC -eq 0 ]'
check "submit reduction: releases as reduced" 'grep -q "\"reason\": \"reduced\"" "$MOCK_LOG"'
check "submit reduction: pushes the reduction file" '[ "$(git --git-dir="$T/origin.git" diff --name-only main "oma/$PID.R1" 2>/dev/null)" = "reductions/$PID.R1.lean" ]'

OUT="$(tools/oma.sh next --kind formalize 2>&1)"
check "formalize: writes statements/<id>.lean" '[ -f statements/opg-x.lean ] && [[ "$OUT" == *"FORMALIZE"* ]]'
OUT="$(tools/oma.sh check opg-x 2>&1)"
check "formalize: check uses the statement file" '[[ "$OUT" == ACCEPTED* ]]'
OUT="$(tools/oma.sh release opg-x too_hard 2>&1)"
check "release: sends the reason" 'grep -q "\"reason\": \"too_hard\"" "$MOCK_LOG" && [ ! -f .oma/leases/opg-x ]'
OUT="$(tools/oma.sh brief $PID 2>&1)"
check "brief: downloads" 'grep -q "BRIEF FOR $PID" .oma/briefs/$PID.txt'
OUT="$(tools/oma.sh status 2>&1)"
check "status: prints live agents" '[[ "$OUT" == *"live agents: 3"* ]]'

echo; [ $FAILS -eq 0 ] && echo "ALL PASSED" || echo "$FAILS FAILED"
exit $FAILS
