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

echo $$ > "$PID_FILE"

while true; do
  {
    echo "=== ARCHON SOP CYCLE $(date -Is) ==="
    if flock -n 9; then
      archon workflow run proof-sop-cycle --cwd "$ROOT" --no-worktree || true
    else
      echo "cycle skipped: lock held"
    fi 9>"$LOCK_FILE"
    echo "=== END ARCHON SOP CYCLE $(date -Is) ==="
    echo
  } >> "$LOG_FILE" 2>&1
  sleep "$INTERVAL_SECONDS"
done
