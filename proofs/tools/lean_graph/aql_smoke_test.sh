#!/usr/bin/env bash
set -euo pipefail

# Smoke-test the local ArangoDB Lean syntax graph used for AST/AQL codebase search.
# Run from /home/goutev/auto/proofs:
#   bash tools/lean_graph/aql_smoke_test.sh

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if [[ -f /home/goutev/.config/arango/env.sh ]]; then
  # shellcheck disable=SC1091
  source /home/goutev/.config/arango/env.sh
elif [[ -f /home/goutev/GITHUB/info-geometry-lean/configs/local/hive_arango.env ]]; then
  # shellcheck disable=SC1091
  source /home/goutev/GITHUB/info-geometry-lean/configs/local/hive_arango.env
elif [[ -f /home/goutev/auto/configs/local/hive_arango.env ]]; then
  # shellcheck disable=SC1091
  source /home/goutev/auto/configs/local/hive_arango.env
fi

AQL_CMD=(python3 tools/lean_graph/aql_query.py)

if ! "${AQL_CMD[@]}" 'RETURN {lean_decls: LENGTH(FOR x IN lean_decls RETURN 1), syntax_decls: LENGTH(FOR x IN syntax_decls RETURN 1)}' >/dev/null 2>&1; then
  export ARANGO_URL='http://127.0.0.1:8529'
  export ARANGO_ENDPOINT="$ARANGO_URL"
  export ARANGO_HOST="$ARANGO_URL"
  export ARANGO_DATABASE='info_geometry'
  export ARANGO_DB="$ARANGO_DATABASE"
  export ARANGO_USERNAME='root'
  export ARANGO_USER="$ARANGO_USERNAME"
  export ARANGO_PASSWORD=''
  export ARANGO_PASS=''
  AQL_CMD=(
    python3 tools/lean_graph/aql_query.py
    --endpoint "$ARANGO_URL"
    --database "$ARANGO_DATABASE"
    --username "$ARANGO_USERNAME"
    --password ''
  )
fi

TMP_COUNTS="$(mktemp)"
TMP_SEARCH="$(mktemp)"
trap 'rm -f "$TMP_COUNTS" "$TMP_SEARCH"' EXIT

"${AQL_CMD[@]}" >"$TMP_COUNTS" <<'AQL'
RETURN {
  lean_decls: LENGTH(FOR x IN lean_decls RETURN 1),
  lean_imports: LENGTH(FOR x IN lean_imports RETURN 1)
}
AQL

python3 - "$TMP_COUNTS" <<'PY'
import json, sys
result = json.load(open(sys.argv[1], encoding='utf-8'))
if not result or not isinstance(result[0], dict):
    raise SystemExit('aql smoke: count query returned no object')
counts = result[0]
for key in ['lean_decls', 'lean_imports']:
    if counts.get(key, 0) <= 0:
        raise SystemExit(f'aql smoke: {key} is empty: {counts}')
print('aql smoke counts:', counts)
PY

"${AQL_CMD[@]}" >"$TMP_SEARCH" <<'AQL'
FOR d IN lean_decls
  FILTER STARTS_WITH(d.name, 'BuresInformationGeodesicFlow.')
     OR STARTS_WITH(d.name, 'CuntzP6MWallpaperBoundary.')
  SORT d.name
  LIMIT 20
  RETURN {name: d.name, kind: d.kind, module: d.module}
AQL

python3 - "$TMP_SEARCH" <<'PY'
import json, sys
rows = json.load(open(sys.argv[1], encoding='utf-8'))
names = {r.get('name') for r in rows}
needles = [
    'BuresInformationGeodesicFlow.modularFlow_zero_time',
    'CuntzP6MWallpaperBoundary.cuntz_p6m_wallpaper_boundary_synthesis',
]
missing = [n for n in needles if n not in names]
if missing:
    raise SystemExit(f'aql smoke: missing expected declarations: {missing}; got {sorted(names)}')
print('aql smoke search matched:', len(rows), 'rows')
PY

echo 'aql smoke passed'
