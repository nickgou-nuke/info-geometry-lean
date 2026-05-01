#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
ENV_FILE="${HIVE_ARANGO_ENV_FILE:-$ROOT_DIR/configs/local/hive_arango.env}"
mkdir -p "$(dirname "$ENV_FILE")"

ENDPOINT="${ARANGO_ENDPOINT:-http://127.0.0.1:8530}"
DATABASE="${ARANGO_DATABASE:-infogeometry}"
USER="${ARANGO_USER:-${ARANGO_USERNAME:-root}}"
PASS="${ARANGO_PASS:-${ARANGO_PASSWORD:-}}"

if [[ -z "$PASS" ]]; then
  echo "[setup] Enter Arango password for user '$USER' (input hidden):" >&2
  read -r -s PASS
  echo >&2
fi

if [[ -z "$PASS" ]]; then
  echo "[setup] ERROR: empty password is not allowed." >&2
  exit 2
fi

cat > "$ENV_FILE" <<EOF
ARANGO_ENDPOINT=$ENDPOINT
ARANGO_DATABASE=$DATABASE
ARANGO_USER=$USER
ARANGO_PASS=$PASS
EOF
chmod 600 "$ENV_FILE"

echo "[setup] Wrote $ENV_FILE (0600)" >&2

ENV_FILE="$ENV_FILE" ENDPOINT="$ENDPOINT" DATABASE="$DATABASE" USER="$USER" PASS="$PASS" python3 - <<'PY'
import os, base64, urllib.request, urllib.error, json
endpoint=os.environ['ENDPOINT'].rstrip('/')
db=os.environ['DATABASE']
user=os.environ['USER']
password=os.environ['PASS']

token=base64.b64encode(f"{user}:{password}".encode()).decode()
req=urllib.request.Request(f"{endpoint}/_db/{db}/_api/cursor", data=json.dumps({'query':'RETURN 1'}).encode('utf-8'), headers={'Content-Type':'application/json','Authorization':f'Basic {token}'}, method='POST')
try:
    with urllib.request.urlopen(req, timeout=10) as r:
        body=json.loads(r.read().decode('utf-8'))
    print(f"[setup] AUTH OK endpoint={endpoint} db={db} user={user} result={body.get('result')}")
except urllib.error.HTTPError as e:
    msg=e.read().decode('utf-8','ignore')
    print(f"[setup] AUTH FAIL status={e.code} body={msg[:200]}")
    raise SystemExit(1)
except Exception as e:
    print(f"[setup] AUTH FAIL {type(e).__name__}: {e}")
    raise SystemExit(1)
PY
