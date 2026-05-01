#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

if [[ $# -gt 0 && "$1" == "--raw-guard" ]]; then
  shift
  exec "${SCRIPT_DIR}/with_arango_env.sh" -- "${SCRIPT_DIR}/run_gemini_guarded.sh" "$@"
fi

if [[ $# -gt 0 && "$1" == "--check" ]]; then
  exec "${SCRIPT_DIR}/with_arango_env.sh" -- "${SCRIPT_DIR}/run_gemini_guarded.sh" "$@"
fi

if [[ $# -gt 0 && ( "$1" == "--help" || "$1" == "-h" ) ]]; then
  exec "${SCRIPT_DIR}/with_arango_env.sh" -- "${SCRIPT_DIR}/run_gemini_guarded.sh" "$@"
fi

exec "${SCRIPT_DIR}/with_arango_env.sh" -- \
  "${SCRIPT_DIR}/run_gemini_guarded.sh" \
  --reason "agent-run gemini with Arango env" \
  -- gemini "$@"
