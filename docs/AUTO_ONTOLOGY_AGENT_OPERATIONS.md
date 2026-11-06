# Auto-Ontology Agent Operations

Operational notes for agents that need the repository declaration ontology.
This guide records the workstation deployment observed on 2026-11-05; the
commands first inspect live state and do not assume that a past report means a
service is still running.

## Active workstation topology

```text
auto-ontology-postgres :5433
       ├── backend REST :3001
       └── ingestion API :3002
frontend / OAuth :3000 ──> backend :3001
MCP :3003 ──> frontend public API :3000
Qwen vLLM :18765 <── socat :58051 <── backend model requests
```

The observed deployment uses the sibling checkout
`/home/goutev/repos/auto-ontology-src`, a PostgreSQL container named
`auto-ontology-postgres` published on host port `5433`, and four transient
`systemd --user` units:

| Unit | Role |
|---|---|
| `auto-ontology-backend.service` | FastAPI REST API on `3001` |
| `auto-ontology-ingestion.service` | Ingestion API on `3002` |
| `auto-ontology-frontend.service` | Next.js UI and OAuth endpoints on `3000` |
| `auto-ontology-llm-58051.service` | Forwards host `127.0.0.1:58051` to vLLM `127.0.0.1:18765` |

The MCP server is a separate `uvx` process on `3003`, configured in the
checkout's `.mcp.json`. The API and MCP are different services. MCP
authentication metadata comes from `GET
/.well-known/oauth-protected-resource/mcp`; an unauthenticated request to
`/mcp` is expected to return `401` and advertise that metadata URL.

These are transient user-systemd units, not installed persistent unit files.
They can disappear when the user manager/session ends. The sibling checkout
and unit definitions were observed on this workstation and may not exist in a
different checkout. Do not print `.env` contents or copy its credentials into
commands, reports, or agent prompts.

## Start or recover the workstation deployment

Run from the repository checkout root. Inspect status before starting anything:

```bash
systemctl --user is-active \
  auto-ontology-backend.service \
  auto-ontology-frontend.service \
  auto-ontology-ingestion.service \
  auto-ontology-llm-58051.service
docker inspect --format '{{.Name}} {{.State.Status}} restart={{.HostConfig.RestartPolicy.Name}}' \
  auto-ontology-postgres
```

If the database container exists but is stopped, start that named container:

```bash
docker start auto-ontology-postgres
```

Start the model bridge and application units after Postgres is accepting
connections:

```bash
systemctl --user start auto-ontology-llm-58051.service
systemctl --user start auto-ontology-backend.service auto-ontology-ingestion.service
systemctl --user start auto-ontology-frontend.service
```

For units that are already active but unhealthy, inspect their logs before
restarting only the affected unit:

```bash
systemctl --user status auto-ontology-backend.service
journalctl --user -u auto-ontology-backend.service -n 100 --no-pager
systemctl --user restart auto-ontology-backend.service
```

Use the matching unit name to inspect/restart frontend, ingestion, or the model
bridge. Do not start the Docker Compose backend/frontend/ingestion stack at the
same time as these host services: both topologies bind ports `3000`–`3002`, and
Compose's Postgres is a separate store (its service port is `5432`; the
populated workstation store is on `5433`). Concurrent starts can target an
empty database or collide on listeners.

## MCP lifecycle

First check whether the configured MCP listener is already running; do not
start a second process on port `3003`:

```bash
curl -fsS http://127.0.0.1:3003/.well-known/oauth-protected-resource/mcp
```

If it is unavailable, start the checked-out MCP package from the repository
root in a long-lived terminal/session:

```bash
env \
  AUTO_ONTOLOGY_API_URL=http://localhost:3000 \
  UV_CACHE_DIR=/tmp/auto-ontology-uv-cache \
  UV_TOOL_DIR=/tmp/auto-ontology-uv-tools \
  uvx --from ./external_refs/auto-ontology/mcp auto-ontology-mcp
```

Keep that process attached to its supervisor/session. It uses OAuth through the
frontend; agents should follow the client's sign-in flow instead of sharing or
embedding a bearer token. The root `.mcp.json` already points to
`http://localhost:3003/mcp`.

## Health and indexed-data checks

These are read-only checks. Run them from the host that owns the listeners:

```bash
curl -fsS http://127.0.0.1:3001/api/health
curl -fsS 'http://127.0.0.1:3001/api/terms?query=InfoGeometry&limit=1'
curl -fsS http://127.0.0.1:58051/v1/models
curl -fsS http://127.0.0.1:3003/.well-known/oauth-protected-resource/mcp
```

At the observation recorded above, the REST query returned `total: 306503`,
the model endpoint listed `nvidia/Qwen3.8-27B-NVFP4`, and the MCP resource
metadata endpoint returned HTTP 200. `GET /mcp` without authorization returns
401 by design. These checks establish API reachability and a returned count;
they do not certify graph completeness, freshness against the current Git
revision, or correctness of a Lean theorem.

The `58051` endpoint is a host-local bridge. From inside a Docker container,
`127.0.0.1` refers to that container; do not copy this model URL into a Compose
container's configuration without setting up and verifying host routing.

## Curated API / MCP query routes and test suites (verified 2026-11-05)

### 1. Curated REST and MCP routes

The FastMCP package in
[`external_refs/auto-ontology/mcp/auto_ontology_mcp/tools.py`](../external_refs/auto-ontology/mcp/auto_ontology_mcp/tools.py)
exposes a curated allow-list of read-only routes from the backend OpenAPI spec
(plus `check_readiness` in `readiness.py` and streaming `ask_question` in
`chat.py`):

| MCP tool name | REST route on `:3001` | Response envelope / role in `info-geometry-lean` |
|---|---|---|
| `search_terms` | `GET /api/terms?query=<q>&limit=<n>` | Returns `{"terms": [...], "total": <int>}` matching declaration names/descriptions |
| `get_term` | `GET /api/terms/{term_id}` | Returns `{"data": {"id", "name", "description", "synonyms", "tables", "related_terms", ...}}` where `tables` lists the owning `lean_module` catalog entry and `related_terms` lists co-module declarations sharing `table__term` (not `term__term` dependency edges) |
| `describe_table` | `GET /api/exploration/tables/{table_id}/details` | Returns `{"data": {"queries": [...], "terms": [...], "terms_total": <int>}}` for a projected Lean module (`catalog_table` of type `lean_module`) |
| `get_term_columns` | `GET /api/terms/{term_id}/column-attributes` | Returns `{"data": [...], "count": <int>, "total": <int>}` (empty for pure Lean declaration projections) |
| `get_term_sql_attributes` | `GET /api/terms/{term_id}/sql-attributes` | Returns `{"data": [...], "count": <int>, "total": <int>}` |
| `get_sql_attribute` | `GET /api/sql-attributes/{attr_id}` | Fetches a single SQL attribute by UUID |
| `check_answerable` | `POST /api/question-entity-coverage` | Grades semantic-layer entity coverage for a natural-language question |

Additional verified FastAPI REST routes on `:3001` (not in the 7-tool MCP allow-list, but implemented in `external_refs/auto-ontology/auto_ontology/server/`):

- `GET /api/exploration/terms/{term_id}/details?skip=0&limit=5` — returns `{"data": {"tables": [...], "tables_total": <int>}}`.
- `GET /api/exploration/nodes/{term_id}/relationships?layer=semantic&skip=0&limit=20` — returns `{"data": {"nodes": [...], "total": <int>}}` (terms sharing a `catalog_table` via `table__term`).
- `POST /api/search/global-search` (and `POST /api/search/global-search/count`) — fulltext search across catalog (`Table`/`Schema`/`Database`) and `Term` with JSON body `{"search_term": "<query>", "filters": {"description": true, "synonyms": true}}`.
- **Routes that do NOT exist** (do not invent): `GET /api/terms/relationships` (`404`) and `GET /api/search` (`404`). Avoid unfiltered `GET /api/exploration/semantic-graph` on the 311k-term store as it computes all pairwise shared-table links before slicing.
- **Schema boundary**: Upstream [`auto_ontology/dal/schema.py`](../external_refs/auto-ontology/auto_ontology/dal/schema.py) defines `catalog_database`, `catalog_schema`, `catalog_table`, `term`, and `table__term`, and does **not** define `term__term`. The `public.term__term` table written by `tools/infra/arango_to_ontology_relationships.py` is a repository-local auxiliary table; query directed Lean dependency edges (`type` / `value`) via ArangoDB (`edges_g_<generation_id>`) or direct SQL on `public.term__term`.

Example verified read-only lookup chain on `:3001` (2026-11-05):

```bash
# 1. Search by declaration substring
curl -fsS 'http://127.0.0.1:3001/api/terms?query=drazin_epistemic_solve_et_coagula_master_synthesis&limit=1'
# -> term_id: 4964a1f8-0974-452d-8a97-5b5b7e74aac7 (total: 1)

# 2. Fetch full term details, owning module table, and related terms
curl -fsS 'http://127.0.0.1:3001/api/terms/4964a1f8-0974-452d-8a97-5b5b7e74aac7'
# -> data.tables[0]: {"id": "82283af1-5e2a-41a1-a935-e9b17a7aa39d", "name": "InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula"}
# -> data.related_terms: 64 linked declaration terms

# 3. Inspect all projected declarations in that Lean module
curl -fsS 'http://127.0.0.1:3001/api/exploration/tables/82283af1-5e2a-41a1-a935-e9b17a7aa39d/details'
# -> data.terms_total: 65
```

### 2. Freshness sentinel checks

Always verify exact declaration sentinels rather than relying on global term
counts. On 2026-11-05:

- Declarations from generation `drazin_epistemic_20261105_a`
  (`drazin_epistemic_solve_et_coagula_master_synthesis`,
  `drazin_cline_polynomial_bicommutant_markov_krein_synthesis`,
  `drazin_clades_4b_5b_7_complete_complement_synthesis`,
  `RoseDrazinPolynomial.isDrazinInverse_clineDrazinShift`,
  `RoseDrazinPolynomial.isDrazinInverse_polynomialDrazinCandidate`, and
  `MarkovDrazin.isDrazinInverse_kemenySnellDeviation`) each returned
  `exact_matches=1` on `:3001`.
- Newer source declarations added after that generation
  (`DrazinAdditiveReverseOrder.isDrazinInverse_add_of_orthogonal`,
  `DrazinAdditiveReverseOrder.isDrazinInverse_mul_of_commute`, and
  `KreinDrazinBoundarySupport.modelBoundaryNormalCone`) returned
  `exact_matches=0`, confirming that the live Postgres store reflects
  `drazin_epistemic_20261105_a` until a new Arango generation is streamed and
  projected via `tools/infra/arango_to_ontology.py` and
  `tools/infra/arango_to_ontology_relationships.py`.

### 3. Automated test suites

Run the following test suites to validate the MCP package, the Arango-to-Postgres
importers, and the live duplicate-candidate grouping semantics:

```bash
# 1. Upstream FastMCP server & tool surface unit tests (88 tests; clean up temp .venv/.pytest_cache afterwards)
uv run --directory external_refs/auto-ontology/mcp pytest -v
rm -rf external_refs/auto-ontology/mcp/.venv external_refs/auto-ontology/mcp/.pytest_cache

# 2. Repository Arango -> Auto-Ontology term and relationship integrity unit tests (15 tests)
PYTHONPATH=src:tools/infra /home/goutev/repos/auto-ontology-src/.venv-ao/bin/python -m unittest \
  tests/test_ontology_relationship_identity.py \
  tests/test_ontology_term_integrity.py -v

# 3. Live read-only Arango duplicate-candidate fingerprint regression (1 test)
set -a && source configs/local/hive_arango.env && set +a && \
  ONTOLOGY_LIVE_TEST=1 PYTHONPATH=src:tools/infra /usr/bin/python3 -m unittest \
  tests/test_ontology_duplicate_candidates_live.py -v

# 4. Source-grounded OpenAPI/schema contract + live REST/MCP endpoint verification (5 tests)
AUTO_ONTOLOGY_LIVE_TEST=1 python3 -m unittest discover \
  -s tests -p test_auto_ontology_package_contract.py -v
```

## Topology assessment

This split host-native setup is convenient for interactive development, and the
currently observed data path works. It is not the most reliable long-running
topology:

- the four user-systemd units are transient and the MCP process has no tracked
  supervisor unit;
- the frontend runs `next dev`, which is a development server;
- the PostgreSQL container's observed restart policy is `no`;
- host-native and Compose deployments can expose duplicate services and
  different Postgres stores under similar names.

For durable single-host operation, choose one deployment owner. Either install
maintained persistent service units with explicit startup dependencies,
restart policies, and health checks for Postgres, backend, ingestion, frontend,
MCP, and the model bridge; or use one Compose stack configured to use the
intended populated database and a verified route to the host model endpoint.
Do not mix the two deployments. Keep MCP OAuth in front of agent access and
keep the local model bridge bound to loopback unless there is a separately
reviewed need to expose it.

## Compose alternative

The upstream checkout includes
[`external_refs/auto-ontology/docker-compose.yml`](../external_refs/auto-ontology/docker-compose.yml).
Use it only as a distinct deployment after checking that the host-managed
listeners are stopped and that the intended Postgres volume/configuration is
selected. Its database and application containers are not interchangeable with
the observed workstation deployment merely because service names match.
Avoid broad `docker compose down`, volume deletion, or database reinitialization
as troubleshooting steps.
