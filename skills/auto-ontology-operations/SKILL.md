---
name: auto-ontology-operations
description: Start, verify, de-conflict, and query the NVIDIA Auto-Ontology semantic layer (:3000 UI, :3001 REST, :3002 Ingestion, :3003 MCP, :5433 Postgres) and the local vLLM reasoning endpoint (http://127.0.0.1:58051/v1 forwards to :18765/v1) for info-geometry-lean.
---

# Auto-Ontology & Local Reasoning Endpoint Operations Skill

Use this skill when starting, diagnosing, refreshing, or querying Auto-Ontology.
Read [the maintained operations guide](../../docs/AUTO_ONTOLOGY_AGENT_OPERATIONS.md)
and [ASTAQLHASH-HOWTO](../../docs/ASTAQLHASH-HOWTO.md) first. Counts below are
historical observations, not readiness or freshness requirements.

## 1. Service Topology & Port Map

| Service | Endpoint / Port | Backing Process / Unit | Role |
|---|---|---|---|
| **Local Reasoning LLM (`vLLM`)** | `http://127.0.0.1:58051/v1` (forwards to `127.0.0.1:18765/v1`) | `auto-ontology-llm-58051.service` (`socat` $\to$ `vllm serve nvidia/Qwen3.8-27B-NVFP4`) | Local OpenAI-compatible reasoning & non-reasoning LLM endpoint used by `auto-ontology` |
| **Populated Postgres Store** | `localhost:5433` (`db=auto_ontology`, `user=ao_user`) | Docker container `auto-ontology-postgres` (`pgvector/pgvector:pg17`) | Holds `306,503` rows in `term` and `2,085,736` rows in `term__term` |
| **Auto-Ontology FastAPI REST** | `http://localhost:3001` | `auto-ontology-backend.service` (`/home/goutev/repos/auto-ontology-src/.venv-ao/bin/python -m auto_ontology.server`) | Term-name search (`/api/terms`) and exploration; no generic Lean dependency endpoint |
| **Auto-Ontology Ingestion** | `http://localhost:3002` | `auto-ontology-ingestion.service` (`python -m auto_ontology.ingestion_service`) | Async catalog & ontology ingestion worker (`/health/live`) |
| **Auto-Ontology MCP Server** | `http://localhost:3003/mcp` | `auto-ontology-mcp.service` (`.venv-ao/bin/auto-ontology-mcp`) | FastMCP HTTP server registered in `.mcp.json` as `nvidia-auto-ontology` |
| **Auto-Ontology Next.js UI** | `http://localhost:3000` | `auto-ontology-frontend.service` (`npx next dev -p 3000`) | Web UI and OAuth authorization server |

## 2. Critical Pitfall: Avoiding the Empty `:5432` Docker Compose Shadow

There are two copies of the Auto-Ontology source tree on the workstation:
1. **Production configured tree (`/home/goutev/repos/auto-ontology-src`)**:
   - Uses `.env` pointing to `POSTGRES_HOST=localhost`, `POSTGRES_PORT=5433` (`auto-ontology-postgres`), and `REASONING_ENDPOINT=http://127.0.0.1:58051/v1`.
2. **Reference submodule (`external_refs/auto-ontology`)**:
   - If `docker compose up` is accidentally run inside `external_refs/auto-ontology`, it starts Docker containers `auto-ontology`, `auto-ontology-ingestion-service`, and `auto-ontology-frontend` connected to an **empty** `postgres` container on `:5432` (`total: 0` terms), shadowing ports `3000–3002`.

**Diagnosis**: A zero query result alone does not identify the cause. Inspect
`/api/health`, the active service configuration, database target, import receipts
and a known source declaration. Use the maintained launcher only after confirming
a stopped or conflicting deployment; do not restart healthy services from a name miss.

## 3. One-Command Startup & Verification

Always use the repository's idempotent startup script (which uses `systemd-run --user` so services survive across agent tool invocations):

```bash
bash tools/infra/start_auto_ontology_services.sh
```

## 4. Querying the Semantic Layer

### Fast, Unauthenticated REST Queries (`http://localhost:3001`)

```bash
# 1. Search declaration names by substring (returns {"terms": [...], "total": N})
curl -fsS "http://127.0.0.1:3001/api/terms?query=cladeFork&skip=0&limit=5"

# 2. Fetch one term by UUID (returns {"data": {..., "tables": [...], "related_terms": [...]}})
curl -fsS "http://127.0.0.1:3001/api/terms/${TERM_ID}"

# 3. Inspect the Lean module table(s) a term belongs to, or all terms in a module table
curl -fsS "http://127.0.0.1:3001/api/exploration/terms/${TERM_ID}/details?skip=0&limit=5"
curl -fsS "http://127.0.0.1:3001/api/exploration/tables/${TABLE_ID}/details?skip=0&limit=20"

# 4. Fulltext global search across Lean module tables and declaration terms
curl -fsS -X POST http://127.0.0.1:3001/api/search/global-search \
  -H 'Content-Type: application/json' \
  -d '{"search_term":"DrazinEpistemicSolveEtCoagula","filters":{"description":true,"synonyms":true}}'
```

Do not call non-existent routes (`GET /api/terms/relationships`, `GET /api/search`) or unfiltered `GET /api/exploration/semantic-graph` on the full store. Verify the package contract and live endpoints with:

```bash
AUTO_ONTOLOGY_LIVE_TEST=1 python3 -m unittest discover \
  -s tests -p test_auto_ontology_package_contract.py -v
```

Query dependency edges through the verified Arango generation as documented in
ASTAQLHASH-HOWTO. Upstream related terms are computed through shared tables;
`related_counts` does not count Lean dependency edges.

### Refreshing the Ontology from ArangoDB (`http://127.0.0.1:8530`)

```bash
# Load the maintained deployment configuration without printing credentials.
# GENERATION_ID must identify a verified completed receipt.
python3 tools/infra/arango_to_ontology.py --arango-db infogeometry --generation-id "$GENERATION_ID"
python3 tools/infra/arango_to_ontology_relationships.py --arango-db infogeometry --generation-id "$GENERATION_ID"
```

These legacy PostgreSQL imports are additive and do not remove stale records or
establish generation membership. See the open
[QMS repair contract](../../docs/ONTOLOGY_PIPELINE_QMS_REPAIR.md) before claiming
a coherent selected snapshot. Use the same generation for both imports.
