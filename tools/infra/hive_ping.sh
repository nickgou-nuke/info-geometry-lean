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

if [[ "$HIVE_PASS" == "CHANGE_ME" ]]; then
  echo "HIVE_ARANGO_PASS is still CHANGE_ME in: $ENV_FILE" >&2
  exit 2
fi

export HIVE_ENDPOINT HIVE_DATABASE HIVE_USER HIVE_PASS

python3 - <<'PY'
import json
import os
import sys
import base64
import urllib.error
import urllib.parse
import urllib.request


endpoint = os.environ["HIVE_ENDPOINT"].rstrip("/")
database = os.environ["HIVE_DATABASE"]
username = os.environ["HIVE_USER"]
password = os.environ["HIVE_PASS"]

db_path = urllib.parse.quote(database, safe="")
url = f"{endpoint}/_db/{db_path}/_api/cursor"
payload = json.dumps({"query": "RETURN { ok: true }"}).encode()

request = urllib.request.Request(
    url,
    data=payload,
    headers={"Content-Type": "application/json"},
    method="POST",
)
token = base64.b64encode(f"{username}:{password}".encode()).decode()
request.add_header("Authorization", f"Basic {token}")

try:
    with urllib.request.urlopen(request, timeout=20) as response:
        body = json.loads(response.read().decode())
except urllib.error.HTTPError as exc:
    detail = exc.read().decode(errors="replace")
    if exc.code in (401, 403):
        print(
            f"Arango auth failed for database '{database}' as user '{username}' "
            f"at {endpoint} (HTTP {exc.code}).",
            file=sys.stderr,
        )
    elif exc.code == 404:
        print(
            f"Arango endpoint or database not found: '{database}' at {endpoint} "
            f"(HTTP 404).",
            file=sys.stderr,
        )
    else:
        print(
            f"Arango ping failed for database '{database}' at {endpoint} "
            f"(HTTP {exc.code}): {detail}",
            file=sys.stderr,
        )
    sys.exit(1)
except Exception as exc:
    print(
        f"Arango ping failed for database '{database}' at {endpoint}: {exc}",
        file=sys.stderr,
    )
    sys.exit(1)

if body.get("error"):
    print(
        f"Arango ping returned an error for database '{database}' at {endpoint}: "
        f"{body}",
        file=sys.stderr,
    )
    sys.exit(1)

print(f"Arango hive auth OK: database='{database}' user='{username}' endpoint='{endpoint}'")
PY
