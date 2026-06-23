#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'USAGE'
usage: aql_smoke_test.sh

Checks the live Arango syntax graph collections:
  syntax_decls, syntax_nodes, ast_child, decl_root

Run through Lake:
  tools/infra/with_arango_env.sh -- lake script run leantrailAQLSmoke
USAGE
  exit 0
fi

TMP_COUNTS="$(mktemp)"
TMP_SEARCH="$(mktemp)"
trap 'rm -f "$TMP_COUNTS" "$TMP_SEARCH"' EXIT

python3 tools/leantrail/aql_query.py >"$TMP_COUNTS" <<'AQL'
RETURN {
  syntax_decls: LENGTH(FOR x IN syntax_decls RETURN 1),
  syntax_nodes: LENGTH(FOR x IN syntax_nodes RETURN 1),
  ast_child: LENGTH(FOR x IN ast_child RETURN 1),
  decl_root: LENGTH(FOR x IN decl_root RETURN 1)
}
AQL

python3 - "$TMP_COUNTS" <<'PY'
import json, sys
result = json.load(open(sys.argv[1], encoding='utf-8'))
if not result or not isinstance(result[0], dict):
    raise SystemExit('aql smoke: count query returned no object')
counts = result[0]
for key in ['syntax_decls', 'syntax_nodes', 'ast_child', 'decl_root']:
    if counts.get(key, 0) <= 0:
        raise SystemExit(f'aql smoke: {key} is empty: {counts}')
print('aql smoke counts:', counts)
PY

python3 tools/leantrail/aql_query.py >"$TMP_SEARCH" <<'AQL'
FOR d IN syntax_decls
  FILTER CONTAINS(d.name, 'Cuntz')
     OR CONTAINS(d.name, 'Poincare')
     OR CONTAINS(d.name, 'Lorentz')
  SORT d.name
  LIMIT 20
  RETURN {name: d.name, keyword: d.keyword, range: d.range}
AQL

python3 - "$TMP_SEARCH" <<'PY'
import json, sys
rows = json.load(open(sys.argv[1], encoding='utf-8'))
if not rows:
    raise SystemExit('aql smoke: expected Cuntz/Poincare/Lorentz declarations, got none')
print('aql smoke search matched:', len(rows), 'rows')
PY

echo 'aql smoke passed'
