#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-/home/goutev/repos/info-geometry-lean}"
SCOPE="${SCOPE:-lean/InfoGeometry/Canonical}"
WORKFLOW="${WORKFLOW:-proof-sop-cycle}"
# Defaults are intentionally unbounded: this is a living cleanup heartbeat.
# Stop it with Ctrl-C. Set MAX_ITERATIONS>0, MAX_STALE_ITERATIONS>0,
# STOP_WHEN_CLEAN=1, or ARCHON_CYCLE_TIMEOUT_SECONDS>0 only when a bounded
# batch run is explicitly desired.
MAX_ITERATIONS="${MAX_ITERATIONS:-0}"
MAX_STALE_ITERATIONS="${MAX_STALE_ITERATIONS:-0}"
STOP_WHEN_CLEAN="${STOP_WHEN_CLEAN:-0}"
ARCHON_CYCLE_TIMEOUT_SECONDS="${ARCHON_CYCLE_TIMEOUT_SECONDS:-0}"
TOP="${TOP:-20}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}"
LOG_DIR="$ROOT/reports/cleanup-loop/$RUN_ID"
LOCK_FILE="$ROOT/reports/cleanup-loop/archon-repo-cleanup.lock"
SUMMARY_FILE="$LOG_DIR/summary.tsv"

mkdir -p "$LOG_DIR" "$(dirname "$LOCK_FILE")"
cd "$ROOT"

# Archon doctor reports Pi as unconfigured if PI_CODING_AGENT is missing or set
# to a boolean sentinel. Point it at the installed Pi binary when available.
if [[ "${PI_CODING_AGENT:-}" == "" || "${PI_CODING_AGENT:-}" == "true" ]]; then
  if command -v pi >/dev/null 2>&1; then
    export PI_CODING_AGENT="$(command -v pi)"
  fi
fi

metric_value() {
  local file="$1" key="$2"
  awk -F': *' -v k="$key" '$1 == k {print $2; found=1; exit} END {if (!found) print 0}' "$file"
}

score_from_report() {
  local file="$1"
  local sorry proxy prop reexport
  sorry="$(metric_value "$file" sorry)"
  proxy="$(metric_value "$file" proxy_field)"
  prop="$(metric_value "$file" prop_socket)"
  reexport="$(metric_value "$file" reexport_proxy)"
  echo $((sorry + proxy + prop + reexport))
}

write_report() {
  local iter="$1" phase="$2" out="$3"
  {
    echo "=== cleanup-loop $RUN_ID iter=$iter phase=$phase $(date -Is) ==="
    echo "root=$ROOT scope=$SCOPE workflow=$WORKFLOW max_iterations=$MAX_ITERATIONS max_stale=$MAX_STALE_ITERATIONS stop_when_clean=$STOP_WHEN_CLEAN timeout=$ARCHON_CYCLE_TIMEOUT_SECONDS"
    python3 tools/quality/proof_heartbeat.py "$SCOPE" --top "$TOP" || true
    echo
    python3 tools/lean4-skills/sorry_analyzer.py "$SCOPE" --format=summary || true
  } > "$out" 2>&1
}

append_summary() {
  local iter="$1" phase="$2" report="$3"
  local sorry proxy prop reexport score
  sorry="$(metric_value "$report" sorry)"
  proxy="$(metric_value "$report" proxy_field)"
  prop="$(metric_value "$report" prop_socket)"
  reexport="$(metric_value "$report" reexport_proxy)"
  score=$((sorry + proxy + prop + reexport))
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
    "$iter" "$phase" "$sorry" "$proxy" "$prop" "$reexport" "$score" "$report" >> "$SUMMARY_FILE"
}

run_archon_cycle() {
  if [[ "$ARCHON_CYCLE_TIMEOUT_SECONDS" -gt 0 ]]; then
    timeout "$ARCHON_CYCLE_TIMEOUT_SECONDS" \
      archon workflow run "$WORKFLOW" --cwd "$ROOT" --no-worktree
  else
    archon workflow run "$WORKFLOW" --cwd "$ROOT" --no-worktree
  fi
}

if [[ ! -f "$SUMMARY_FILE" ]]; then
  printf "iter\tphase\tsorry\tproxy_field\tprop_socket\treexport_proxy\tscore\treport\n" > "$SUMMARY_FILE"
fi

best_score=999999999
stale_iterations=0
iter=1

while true; do
  if [[ "$MAX_ITERATIONS" -gt 0 && "$iter" -gt "$MAX_ITERATIONS" ]]; then
    echo "cleanup-loop: reached MAX_ITERATIONS=$MAX_ITERATIONS. summary=$SUMMARY_FILE"
    exit 3
  fi

  before="$LOG_DIR/iter-$(printf '%03d' "$iter")-before.log"
  after="$LOG_DIR/iter-$(printf '%03d' "$iter")-after.log"
  archon_log="$LOG_DIR/iter-$(printf '%03d' "$iter")-archon.log"

  write_report "$iter" before "$before"
  append_summary "$iter" before "$before"
  before_score="$(score_from_report "$before")"

  if [[ "$before_score" -eq 0 ]]; then
    echo "cleanup-loop: clean before iteration $iter; continuing heartbeat. summary=$SUMMARY_FILE"
    if [[ "$STOP_WHEN_CLEAN" == "1" ]]; then
      echo "cleanup-loop: STOP_WHEN_CLEAN=1; stopping. summary=$SUMMARY_FILE"
      exit 0
    fi
  fi

  if ! flock -n 9; then
    echo "cleanup-loop: another cleanup loop is active; lock=$LOCK_FILE" | tee -a "$archon_log"
    exit 75
  fi

  {
    echo "=== archon workflow run iter=$iter $(date -Is) ==="
    echo "before_score=$before_score"
    run_archon_cycle
    echo "=== archon workflow done iter=$iter $(date -Is) ==="
  } > "$archon_log" 2>&1 || {
    code=$?
    echo "cleanup-loop: workflow exited nonzero/timeout code=$code; see $archon_log" | tee -a "$archon_log"
  }
  flock -u 9

  write_report "$iter" after "$after"
  append_summary "$iter" after "$after"
  after_score="$(score_from_report "$after")"

  if [[ "$after_score" -eq 0 ]]; then
    echo "cleanup-loop: clean after iteration $iter; continuing heartbeat. summary=$SUMMARY_FILE"
    if [[ "$STOP_WHEN_CLEAN" == "1" ]]; then
      echo "cleanup-loop: STOP_WHEN_CLEAN=1; stopping. summary=$SUMMARY_FILE"
      exit 0
    fi
  fi

  if [[ "$after_score" -lt "$best_score" ]]; then
    best_score="$after_score"
    stale_iterations=0
  else
    stale_iterations=$((stale_iterations + 1))
  fi

  if [[ "$MAX_STALE_ITERATIONS" -gt 0 && "$stale_iterations" -ge "$MAX_STALE_ITERATIONS" ]]; then
    echo "cleanup-loop: stopped after $stale_iterations stale iterations; best_score=$best_score summary=$SUMMARY_FILE"
    exit 2
  fi

  iter=$((iter + 1))
done 9>"$LOCK_FILE"
