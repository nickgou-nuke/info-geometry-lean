#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-/home/goutev/repos/info-geometry-lean}"
INTERVAL_SECONDS="${INTERVAL_SECONDS:-600}"
LOG_DIR="$ROOT/reports/heartbeat"
LOG_FILE="$LOG_DIR/archon-proof-sop-cycle.log"
LOCK_FILE="$LOG_DIR/archon-proof-sop-cycle.lock"
PID_FILE="$LOG_DIR/archon-proof-sop-cycle.pid"

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

while true; do
  {
    echo "=== ARCHON SOP CYCLE $(date -Is) ==="
    echo "pid=$$ root=$ROOT interval=${INTERVAL_SECONDS}s pi=${PI_CODING_AGENT:-unset}"
    python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 20 || true
    python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary || true
    if flock -n 9; then
      timeout "${ARCHON_CYCLE_TIMEOUT_SECONDS:-1800}" \
        archon workflow run proof-sop-cycle --cwd "$ROOT" --no-worktree || true
    else
      echo "cycle skipped: lock held"
    fi 9>"$LOCK_FILE"
    python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 20 || true
    echo "=== END ARCHON SOP CYCLE $(date -Is) ==="
    echo
  } >> "$LOG_FILE" 2>&1
  sleep "$INTERVAL_SECONDS"
done
