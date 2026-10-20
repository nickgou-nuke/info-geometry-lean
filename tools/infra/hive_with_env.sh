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

HIVE_ENDPOINT="${HIVE_ARANGO_ENDPOINT:-${HIVE_ENDPOINT:-}}"
HIVE_DATABASE="${HIVE_ARANGO_DATABASE:-${HIVE_DATABASE:-}}"
HIVE_USER="${HIVE_ARANGO_USER:-${HIVE_ARANGO_USERNAME:-${HIVE_USER:-}}}"
HIVE_PASS="${HIVE_ARANGO_PASS:-${HIVE_ARANGO_PASSWORD:-${HIVE_PASS:-}}}"
: "${HIVE_ENDPOINT:?HIVE_ARANGO_ENDPOINT or HIVE_ENDPOINT missing}"
: "${HIVE_DATABASE:?HIVE_ARANGO_DATABASE or HIVE_DATABASE missing}"
: "${HIVE_USER:?HIVE_ARANGO_USER or HIVE_USER missing}"
: "${HIVE_PASS:?HIVE_ARANGO_PASS or HIVE_PASS missing}"

HIVE_PYTHON_BIN="${ARANGO_PYTHON_BIN:-$ROOT_DIR/.venv-py312/bin/python}"
if [[ ! -x "$HIVE_PYTHON_BIN" ]]; then
  HIVE_PYTHON_BIN="python3"
fi

export PYTHONPATH="$ROOT_DIR:$ROOT_DIR/src${PYTHONPATH:+:$PYTHONPATH}"

exec "$HIVE_PYTHON_BIN" "$ROOT_DIR/tools/infra/hive_arango_queue.py" \
  --endpoint "$HIVE_ENDPOINT" \
  --database "$HIVE_DATABASE" \
  --username "$HIVE_USER" \
  --password "$HIVE_PASS" \
  "$@"
