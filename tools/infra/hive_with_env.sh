#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
ENV_FILE="${HIVE_ARANGO_ENV_FILE:-$ROOT_DIR/configs/local/hive_arango.env}"

if [[ ! -f "$ENV_FILE" ]]; then
  echo "Missing env file: $ENV_FILE" >&2
  echo "Create it from: $ROOT_DIR/configs/local/hive_arango.env.example" >&2
  exit 2
fi

# shellcheck disable=SC1090
set -a; source "$ENV_FILE"; set +a

: "${ARANGO_ENDPOINT:?ARANGO_ENDPOINT missing}"
: "${ARANGO_DATABASE:?ARANGO_DATABASE missing}"
: "${ARANGO_USER:?ARANGO_USER missing}"
: "${ARANGO_PASS:?ARANGO_PASS missing}"

HIVE_PYTHON_BIN="${ARANGO_PYTHON_BIN:-$ROOT_DIR/.venv-py312/bin/python}"
if [[ ! -x "$HIVE_PYTHON_BIN" ]]; then
  HIVE_PYTHON_BIN="python3"
fi

exec "$HIVE_PYTHON_BIN" "$ROOT_DIR/tools/infra/hive_arango_queue.py" \
  --endpoint "$ARANGO_ENDPOINT" \
  --database "$ARANGO_DATABASE" \
  --username "$ARANGO_USER" \
  --password "$ARANGO_PASS" \
  "$@"
