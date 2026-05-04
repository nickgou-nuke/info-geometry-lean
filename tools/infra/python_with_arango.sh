#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
ARANGO_PYTHON_BIN="${ARANGO_PYTHON_BIN:-$ROOT_DIR/.venv-py312/bin/python}"
if [[ ! -x "$ARANGO_PYTHON_BIN" ]]; then
  ARANGO_PYTHON_BIN="python3"
fi

exec "$(cd "$(dirname "$0")" && pwd)/with_arango_env.sh" -- "$ARANGO_PYTHON_BIN" "$@"
