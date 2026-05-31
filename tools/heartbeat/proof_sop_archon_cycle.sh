#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-/home/goutev/repos/info-geometry-lean}"
SCOPE="${SCOPE:-lean}"
WORKFLOW="${WORKFLOW:-proof-purification-pipeline}"
INTERVAL_SECONDS="${INTERVAL_SECONDS:-0}"
PROOF_PROXY_DIFF_GATE="${PROOF_PROXY_DIFF_GATE:-1}"
SEMANTIC_REGRESSION_GATE="${SEMANTIC_REGRESSION_GATE:-1}"
REQUIRE_COMMITTED_BASELINE="${REQUIRE_COMMITTED_BASELINE:-1}"
REQUIRE_PUSHED_BASELINE="${REQUIRE_PUSHED_BASELINE:-1}"
AUTO_COMMIT_BEFORE_AUDIT="${AUTO_COMMIT_BEFORE_AUDIT:-0}"
AUTO_PUSH_BEFORE_AUDIT="${AUTO_PUSH_BEFORE_AUDIT:-1}"
AUTO_COMMIT_MESSAGE="${AUTO_COMMIT_MESSAGE:-proof-cleanup: commit cycle before audit}"
LOG_DIR="$ROOT/reports/heartbeat"
LOG_FILE="$LOG_DIR/archon-proof-sop-cycle.log"
LOCK_FILE="$LOG_DIR/archon-proof-sop-cycle.lock"
PID_FILE="$LOG_DIR/archon-proof-sop-cycle.pid"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)-$$}"

mkdir -p "$LOG_DIR"
cd "$ROOT"

# Archon doctor reports Pi as unconfigured if PI_CODING_AGENT is missing or set
# to a boolean sentinel.  Point it at the installed Pi binary when available.
if [[ "${PI_CODING_AGENT:-}" == "" || "${PI_CODING_AGENT:-}" == "true" ]]; then
  if command -v pi >/dev/null 2>&1; then
    export PI_CODING_AGENT="$(command -v pi)"
  fi
fi

echo $$ > "$PID_FILE"

run_committed_baseline_gate() {
  local phase="$1"
  local args=()
  if [[ "$REQUIRE_PUSHED_BASELINE" == "1" ]]; then
    args+=(--require-pushed)
  fi
  if [[ "$REQUIRE_COMMITTED_BASELINE" == "1" ]]; then
    python3 tools/quality/committed_baseline_gate.py "$SCOPE" "${args[@]}"
  fi
}

scope_has_changes() {
  ! git diff --quiet -- "$SCOPE" ||
    ! git diff --cached --quiet -- "$SCOPE" ||
    [[ -n "$(git ls-files --others --exclude-standard -- "$SCOPE")" ]]
}

commit_scope_before_audit() {
  if [[ "$AUTO_COMMIT_BEFORE_AUDIT" == "1" ]] && scope_has_changes; then
    git add -A -- "$SCOPE"
    git commit -m "$AUTO_COMMIT_MESSAGE"
    if [[ "$AUTO_PUSH_BEFORE_AUDIT" == "1" ]]; then
      git push
    fi
  fi
}

cycle_iter=1

while true; do
  {
    echo "=== ARCHON SOP CYCLE $(date -Is) ==="
    echo "pid=$$ root=$ROOT scope=$SCOPE workflow=$WORKFLOW post_cycle_sleep=${INTERVAL_SECONDS}s proxy_diff_gate=$PROOF_PROXY_DIFF_GATE semantic_regression_gate=$SEMANTIC_REGRESSION_GATE committed_baseline=$REQUIRE_COMMITTED_BASELINE pushed_baseline=$REQUIRE_PUSHED_BASELINE auto_commit_before_audit=$AUTO_COMMIT_BEFORE_AUDIT pi=${PI_CODING_AGENT:-unset}"
    baseline_ref="$(git rev-parse HEAD)"
    if ! run_committed_baseline_gate before; then
      echo "cycle stopped: audited files must be committed and pushed before pre-cycle audit"
      exit 92
    fi
    python3 tools/quality/proof_heartbeat.py lean --top 20 || true
    python3 tools/quality/semantic_vacuity_gate.py lean --fail-on none --top 20 || true
    python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary || true
    if flock -n 9; then
      if [[ -d "$ROOT/tools/archon" ]] && command -v bun >/dev/null 2>&1; then
        timeout "${ARCHON_CYCLE_TIMEOUT_SECONDS:-1800}" \
          bash -lc 'cd "$0/tools/archon" && bun run cli workflow run "$1" --cwd "$0" --no-worktree' "$ROOT" "$WORKFLOW" || true
      else
        timeout "${ARCHON_CYCLE_TIMEOUT_SECONDS:-1800}" \
        archon workflow run "$WORKFLOW" --cwd "$ROOT" --no-worktree || true
      fi
    else
      echo "cycle skipped: lock held"
    fi 9>"$LOCK_FILE"
    commit_scope_before_audit
    if ! run_committed_baseline_gate after; then
      echo "cycle stopped: workflow produced uncommitted or unpushed audited files; no files restored"
      exit 92
    fi
    after_ref="$(git rev-parse HEAD)"
    if [[ "$PROOF_PROXY_DIFF_GATE" == "1" ]]; then
      if [[ "$after_ref" != "$baseline_ref" ]] &&
          ! python3 tools/quality/proof_proxy_diff_gate.py --base "$baseline_ref" "$SCOPE"; then
        echo "cycle stopped: proof proxy diff gate failed against committed ref $baseline_ref..HEAD; no files restored"
        exit 90
      fi
    fi
    if [[ "$SEMANTIC_REGRESSION_GATE" == "1" ]]; then
      if [[ "$after_ref" != "$baseline_ref" ]] &&
          ! python3 tools/quality/semantic_regression_gate.py --base "$baseline_ref" "$SCOPE"; then
        echo "cycle stopped: semantic regression gate failed against committed ref $baseline_ref..HEAD; no files restored"
        exit 91
      fi
    fi
    python3 tools/quality/proof_heartbeat.py lean --top 20 || true
    python3 tools/quality/semantic_vacuity_gate.py lean --fail-on none --top 20 || true
    echo "=== END ARCHON SOP CYCLE $(date -Is) ==="
    echo
  } >> "$LOG_FILE" 2>&1
  if [[ "$INTERVAL_SECONDS" -gt 0 ]]; then
    sleep "$INTERVAL_SECONDS"
  fi
  cycle_iter=$((cycle_iter + 1))
done
