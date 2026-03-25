#!/usr/bin/env bash
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  if [ -x "$HOME/.elan/bin/lake" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
  else
    echo "error: 'lake' is not on PATH." >&2
    echo "Install Lean toolchain manager (elan), then re-run this script." >&2
    exit 127
  fi
fi

exec lake build "$@"
exec python3 tools/infra/run_locked_lake_build.py "$@"
