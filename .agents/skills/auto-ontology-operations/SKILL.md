---
name: auto-ontology-operations
description: Start, inspect, recover, or query this repository's Auto-Ontology services. Use when an agent needs the Lean declaration ontology REST API or MCP; not for Lean proof authority or unrelated Docker stacks.
metadata:
  short-description: Operate the Auto-Ontology services
---

# Auto-Ontology operations

Use the repository's [operations guide](../../../docs/AUTO_ONTOLOGY_AGENT_OPERATIONS.md)
for the observed topology, exact commands, health probes, and OAuth behavior.

Before starting services, inspect their state. On the current workstation the
active deployment is host-native: transient `systemd --user` units for backend,
frontend, ingestion, and the Qwen bridge; Docker Postgres on `5433`; and a
separate MCP process on `3003`. The populated database is the
`auto-ontology-postgres` container. The upstream Compose file is an alternative
deployment and must not be started alongside the host services on ports
`3000`–`3002`.

Operational sequence:

1. Confirm the repo root and inspect `systemctl --user` and Docker state.
2. Start the existing Postgres container only if it is stopped.
3. Start the model bridge, backend and ingestion units, then frontend; use the
   guide's host health probes to verify readiness.
4. Check MCP resource metadata on `3003` before launching MCP. If unavailable,
   run the checked-out MCP package in a supervised long-lived session. Do not
   duplicate an already-bound listener.
5. Use the REST API for lexical/semantic navigation or MCP after OAuth. Treat
   API results as navigation evidence; inspect Lean owners and kernel checks
   for mathematical claims.

Keep credentials out of commands and output. Do not start the Compose stack as
a generic repair, delete containers or volumes, or claim graph freshness from
an API response. The current `58051` model bridge is loopback-only and routes
to vLLM at `18765`; container clients need separately verified routing.

## Verified `external_refs/auto-ontology` Routes & Contract Test

Never invent routes (such as `GET /api/terms/relationships` or `GET /api/search`).
Check [`external_refs/auto-ontology/mcp/auto_ontology_mcp/auto-ontology-api.json`](../../../external_refs/auto-ontology/mcp/auto_ontology_mcp/auto-ontology-api.json)
and [`external_refs/auto-ontology/mcp/auto_ontology_mcp/tools.py`](../../../external_refs/auto-ontology/mcp/auto_ontology_mcp/tools.py):

- **FastAPI REST (`http://127.0.0.1:3001`)**:
  - `GET /api/health` and `GET /api/semantic-compilation/status`
  - `GET /api/terms?query=<substr>&skip=0&limit=20` (returns `{"terms": [...], "total": N, ...}`)
  - `GET /api/terms/{term_id}` (returns `{"data": {"id", "name", "tables", "related_terms", ...}}`)
  - `GET /api/exploration/terms/{term_id}/details?skip=0&limit=20` (returns `{"data": {"tables": [...], "tables_total": N}}`)
  - `GET /api/exploration/tables/{table_id}/details?skip=0&limit=20` (returns `{"data": {"queries": [], "terms": [...], "terms_total": N}}`)
  - `GET /api/exploration/nodes/{term_id}/relationships?layer=semantic&skip=0&limit=20` (terms sharing a Lean module table)
  - `POST /api/search/global-search` with JSON `{"search_term": "...", "filters": {"description": true, "synonyms": true}}`
- **Curated MCP tools (`http://127.0.0.1:3003/mcp`)**:
  - `check_readiness`, `search_terms`, `get_term`, `get_term_columns`, `get_term_sql_attributes`, `get_sql_attribute`, `describe_table`, `check_answerable`, `ask_question`.
- **Schema boundary**:
  - Upstream `auto-ontology` links terms to module tables via `public.table__term`; its `related_terms` are co-module terms, not Lean dependency edges.
  - Directed theorem dependency edges (`type` / `value`) must be queried in ArangoDB (`edges_g_<generation_id>`) or via SQL on the auxiliary `public.term__term` table written by `tools/infra/arango_to_ontology_relationships.py`.
- **Verification command**:
  ```bash
  AUTO_ONTOLOGY_LIVE_TEST=1 python3 -m unittest discover \
    -s tests -p test_auto_ontology_package_contract.py -v
  ```
