#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
ENV_FILE="${HIVE_ARANGO_ENV_FILE:-$ROOT_DIR/configs/local/hive_arango.env}"

if [[ ! -f "$ENV_FILE" ]]; then
  echo "[with_arango_env] Missing env file: $ENV_FILE" >&2
  echo "[with_arango_env] Run: tools/infra/arango_access_setup.sh" >&2
  exit 2
fi

unset ARANGO_ENDPOINT ARANGO_DATABASE ARANGO_USER ARANGO_PASS ARANGO_USERNAME ARANGO_PASSWORD

set -a
# shellcheck disable=SC1090
source "$ENV_FILE"
set +a

# Alias support
export ARANGO_ENDPOINT="${ARANGO_ENDPOINT:-http://127.0.0.1:8530}"
export ARANGO_DATABASE="${ARANGO_DATABASE:-infogeometry}"
export ARANGO_USER="${ARANGO_USER:-${ARANGO_USERNAME:-}}"
export ARANGO_PASS="${ARANGO_PASS:-${ARANGO_PASSWORD:-}}"
export ARANGO_USERNAME="$ARANGO_USER"
export ARANGO_PASSWORD="$ARANGO_PASS"

if [[ $# -eq 0 ]]; then
  echo "Usage: tools/infra/with_arango_env.sh -- <command> [args...]" >&2
  exit 2
fi

if [[ "$1" == "--" ]]; then
  shift
fi

exec "$@"
