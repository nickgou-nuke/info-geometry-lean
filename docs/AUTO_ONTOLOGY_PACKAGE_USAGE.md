# Auto-Ontology package and repository graph usage

This repository uses two related systems with different responsibilities.

| Component | Role | Authoritative input/output |
|---|---|---|
| Repository declaration exporter and Arango graph | Builds the Lean declaration dependency graph from compiler output | Lean declarations and `type`/`value` dependency edges, stored in an immutable Arango generation |
| `external_refs/auto-ontology/mcp` package | Exposes an Auto-Ontology deployment's public semantic API to MCP clients | Read-only term/catalog tools and the deployment's question-answering endpoint |
| REST API on port 3001 | Scriptable term search and inspection | Additive Auto-Ontology PostgreSQL projection |

The MCP package does not compile Lean, export declarations, or create the
compiler dependency graph. The repo-owned Arango-to-Auto-Ontology importers
populate terms and relationships after graph generation. The MCP package is a
client of the resulting Auto-Ontology API. Neither MCP related-term counts nor
shared catalog-table relationships should be interpreted as Lean dependency
edges; query those from the selected Arango generation.

## Checked-out package

The `external_refs/auto-ontology` submodule is pinned at
`2a24f5d34ef6b6e168a7f22d308504d3ab36a198` in the reviewed checkout. Its MCP
distribution is `auto-ontology-mcp` version `1.1.0`, declared in
`external_refs/auto-ontology/mcp/pyproject.toml`. Package implementation and
tool list are in `mcp/auto_ontology_mcp/`; upstream package documentation is in
`external_refs/auto-ontology/mcp/README.md` and
`external_refs/auto-ontology/docs/mcp.md`.

## Connect an MCP client

The repository root `.mcp.json` configures the client endpoint:

```json
{
  "mcpServers": {
    "nvidia-auto-ontology": {
      "type": "http",
      "url": "http://localhost:3003/mcp"
    }
  }
}
```

The server needs the public frontend URL, not the backend REST URL:

```bash
AUTO_ONTOLOGY_API_URL=http://localhost:3000
```

For the host deployment documented in
[`AUTO_ONTOLOGY_AGENT_OPERATIONS.md`](AUTO_ONTOLOGY_AGENT_OPERATIONS.md), port
3003 is already served by the separate MCP process. Check before starting a
second instance:

```bash
curl -fsS http://127.0.0.1:3003/.well-known/oauth-protected-resource/mcp
```

If that endpoint is unavailable, launch the checked-out package from the repo
root and keep the process under a long-lived supervisor/session:

```bash
env \
  AUTO_ONTOLOGY_API_URL=http://localhost:3000 \
  UV_CACHE_DIR=/tmp/auto-ontology-uv-cache \
  UV_TOOL_DIR=/tmp/auto-ontology-uv-tools \
  uvx --from ./external_refs/auto-ontology/mcp auto-ontology-mcp
```

The package implements OAuth. The MCP client must complete the interactive
sign-in through the frontend; do not put bearer tokens or database credentials
in `.mcp.json`. A 401 from `/mcp` without a signed-in client is expected. The
OAuth metadata endpoint returning 200 confirms discovery, not authenticated
tool execution.

## Available MCP tools and suitable use

The curated package tools are `search_terms`, `get_term`, `get_term_columns`,
`get_term_sql_attributes`, `get_sql_attribute`, `describe_table`,
`check_answerable`, `check_readiness`, and `ask_question`. The first group
inspects the semantic catalog; `ask_question` invokes the deployment's
text-to-SQL agent. These are read operations. For this repository, use term
search to locate an imported Lean declaration and its source location. Then
inspect that Lean owner and use the compiler-backed graph for dependency
evidence. Do not use `ask_question` as a theorem search or proof checker.

Without OAuth, the documented read-only REST surface is available directly:

```bash
curl -fsS 'http://127.0.0.1:3001/api/terms?query=Krein&limit=5'
curl -fsS 'http://127.0.0.1:3001/api/health'
```

`/api/terms?query=...` is a case-insensitive substring search over imported
term names. It does not search Lean source, docstrings, or dependency edges. A
zero-result query is not proof that a declaration is absent; check service
health, the exact declaration name, and the projection's import evidence.

## Refresh the repository declaration ontology

For a full online declaration-graph refresh, follow the immutable-generation
workflow in [`ASTAQLHASH-HOWTO.md`](ASTAQLHASH-HOWTO.md#default-agent-workflow-online-immutable-arango-generation).
In outline, inspect active compiler processes and pinned build artifacts, then
run the locked full-scope exporter:

```bash
python3 tools/infra/refresh_decl_graph.py \
  --stream --run-mode exe \
  --import-root InfoGeometry.All --namespace InfoGeometry \
  --arango-db infogeometry
```

Record the exact generation ID printed by the exporter. Verify its receipt is
`complete`, its full import scope and fingerprint match this checkout, its
declaration count is nonzero, its valid and emitted edge counts agree, and it
has no dangling endpoints. Query dependencies by that generation ID; never
silently fall back to the mutable legacy `decls`/`edges` collections.

The downstream term and relationship importers are **additive legacy
projections**, not generation-pinned publication. Only after inspecting their
current source, target database, and row counts, run both with the exact same
generation ID and explicit additive acknowledgment:

```bash
python3 tools/infra/arango_to_ontology.py \
  --arango-db infogeometry --generation-id "$GENERATION_ID" --legacy-additive
python3 tools/infra/arango_to_ontology_relationships.py \
  --arango-db infogeometry --generation-id "$GENERATION_ID" --legacy-additive
```

Their success does not establish an atomic or coherent snapshot in PostgreSQL;
old rows remain, and REST reads are not pinned to an Arango generation. Record
that limitation when reporting freshness. The package's MCP server does not
change these importer semantics.

## Health and evidence boundaries

Check the active deployment before starting services or importing data. The
host deployment observed on 2026-11-05 used PostgreSQL port 5433, REST port
3001, frontend/OAuth port 3000, MCP port 3003, and model bridge port 58051. The
Compose deployment in the submodule uses a separate PostgreSQL store; do not
start it alongside host services or assume it contains the same data.

Health endpoints establish reachability only. MCP OAuth metadata establishes
OAuth discovery only. REST term counts establish a count only. Arango
generation receipts and exact generation queries establish graph evidence at
their recorded scope. Lean source inspection and kernel checks remain the
authority for mathematical claims. See the repo's
[`ONTOLOGY_UNIFICATION_PLAYBOOK.md`](ONTOLOGY_UNIFICATION_PLAYBOOK.md) for
typed lane mapping, duplicate review, and freshness sentinels.
