#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "Usage: $0 <lean-file> [top-n]"
  echo "Example: $0 lean/InfoGeometry/Architecture/OctonionicFlow.lean 15"
  exit 2
fi

LEAN_FILE="$1"
TOP_N="${2:-15}"

if [[ ! -f "$LEAN_FILE" ]]; then
  echo "error: file not found: $LEAN_FILE"
  exit 2
fi

RAW_LOG="$(mktemp /tmp/lean-profile-XXXXXX.log)"

echo "[profile] running trace profiler on: $LEAN_FILE"
lake env lean -Dtrace.profiler=true "$LEAN_FILE" >"$RAW_LOG" 2>&1

echo
echo "[profile] top ${TOP_N} Elab.command entries (seconds):"
awk '
  match($0, /^\[Elab\.command\] \[([0-9.]+)\] (.*)$/, m) {
    t = m[1] + 0
    cmd = m[2]
    gsub(/[[:space:]]+/, " ", cmd)
    print t "\t" cmd
  }
' "$RAW_LOG" | sort -nr -k1,1 | head -n "$TOP_N"

echo
echo "[profile] top ${TOP_N} Elab.step entries (seconds):"
awk '
  match($0, /^\[Elab\.step\] \[([0-9.]+)\] (.*)$/, m) {
    t = m[1] + 0
    step = m[2]
    gsub(/[[:space:]]+/, " ", step)
    print t "\t" step
  }
' "$RAW_LOG" | sort -nr -k1,1 | head -n "$TOP_N"

echo
echo "[profile] raw trace log: $RAW_LOG"

