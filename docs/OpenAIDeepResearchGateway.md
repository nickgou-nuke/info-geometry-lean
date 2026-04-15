# OpenAI Deep Research Gateway (Two-Layer MCP)

This repository now supports a two-layer deep-research loop:

1. Codex-facing MCP gateway (`tools/infra/openai_deep_research_gateway.py`)
2. OpenAI Responses API deep-research execution (`o4-mini-deep-research` or `o3-deep-research`)

Optional third layer:
- nested remote MCP data source (`search`/`fetch`) for private corp data.

## Why two layers

The Codex-facing server is a control plane (`dr_start` / `dr_status` / `dr_result`).
The deep-research model itself performs browsing/retrieval/tool execution.

This keeps local agent tools stable while allowing model-side data-source mixing:
- `web_search_preview`
- `file_search`
- `mcp` (remote nested datasource)
- `code_interpreter`

## Dependencies

Install runtime deps in the active environment:

```bash
.venv/bin/pip install "openai>=1.0.0" "fastmcp>=0.2.0"
```

Required env vars:

```bash
export OPENAI_API_KEY="..."
```

Optional env vars:

```bash
export OPENAI_DR_DEFAULT_MODEL="o4-mini-deep-research"
export OPENAI_DR_TIMEOUT_SEC="3600"
export OPENAI_DR_MCP_TRANSPORT=""           # empty => default FastMCP run
export OPENAI_DR_MCP_HOST="127.0.0.1"
export OPENAI_DR_MCP_PORT="8787"
```

## Gateway tools

Implemented in `tools/infra/openai_deep_research_gateway.py`:

- `dr_preflight_rewrite` — optional rewrite of rough asks into DR briefs
- `dr_start` — starts background deep-research job, returns `response_id`
- `dr_status` — poll job status
- `dr_result` — fetch final text and tool traces
- `dr_run_blocking` — convenience blocking runner
- `dr_ingest_result_to_packet` — writes final result into `handover/injections` packet segment

## Run the gateway

```bash
python3 tools/infra/openai_deep_research_gateway.py
```

## Attach gateway to Codex CLI

For a remotely hosted MCP endpoint:

```bash
codex mcp add deepresearch --url https://YOUR_HOST/mcp
codex mcp list
```

Then call:
1. `dr_start`
2. `dr_status` until `completed`
3. `dr_result`
4. optional `dr_ingest_result_to_packet`

## Nested datasource MCP (for private corpus)

Use `tools/infra/openai_deep_research_datasource_mcp_example.py` as the template.

Deep-research-compatible nested MCP contract:
- `search(query)` -> one text content item containing JSON with `results`
- `fetch(id)` -> one text content item containing JSON with document body

When passed to `dr_start`, the gateway emits nested MCP config with:

```json
{"type":"mcp", "server_url":"...", "require_approval":"never"}
```

## Injection lane integration

`dr_ingest_result_to_packet` attaches completed DR output to a packet segment:
- writes DR text to `creative_notes`, `enriched_context`, or both
- extracts trace URLs into `literature_evidence`
- keeps packet schema valid and appends history event

This closes the loop:

`OpenAI DR -> packet segment -> translated/gated/accepted lanes`.

## Copilot / Gemini CLI / Hermes mirror

Use the same packet contract and promote flow.

- Copilot workflow mirror: `.agents/workflows/repo-topic-deep-research/`
- Gemini creative prompt template:
  `skills/repo-topic-deep-research/templates/gemini_cli_prompt_template.md`
- Hermes verification template:
  `skills/repo-topic-deep-research/templates/hermes_enrichment_prompt_template.md`

Deep Research can be used as an additional provider stage, without changing the lane schema.
