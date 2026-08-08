#!/usr/bin/env bash
set -euo pipefail

# Smoke-test the repository-level Lean module graph in ArangoDB.
# Defaults match import_module_graph_arango.py.

cd "$(dirname "$0")/../.."
ENV_FILE="${ARANGO_ENV_FILE:-/tmp/empty-arango-env}"
touch "$ENV_FILE"

python3 tools/lean_graph/aql_query.py \
  --env-file "$ENV_FILE" \
  --endpoint "${ARANGO_URL:-${ARANGO_ENDPOINT:-http://localhost:8529}}" \
  --database "${ARANGO_DB:-${ARANGO_DATABASE:-info_geometry}}" \
  --username "${ARANGO_USER:-${ARANGO_USERNAME:-root}}" \
  --password "${ARANGO_PASSWORD:-${ARANGO_PASS:-}}" <<'AQL'
RETURN {
  modules: LENGTH(FOR m IN lean_modules RETURN 1),
  imports: LENGTH(FOR e IN lean_imports RETURN 1),
  topImported: (
    FOR e IN lean_imports
      COLLECT target = e._to WITH COUNT INTO c
      SORT c DESC
      LIMIT 5
      LET m = DOCUMENT(target)
      RETURN {module: m.name, importedBy: c}
  )
}
AQL
