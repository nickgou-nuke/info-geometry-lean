# ArangoDB Management and Architecture

> Status: `reference memory`
> Audited: 2026-05-02 (Alexandria lane isolation and PDF-to-DAG-brain section refreshed 2026-11-24 against commit `9bbab55c38`)
> Note: Re-audit LeanTrail/Hive sections against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CANONICAL_AGENT_PIPELINE.md](CANONICAL_AGENT_PIPELINE.md), [tools/alexandria/README.md](../tools/alexandria/README.md), [configs/alexandria/README.md](../configs/alexandria/README.md)

This document defines the role, lifecycle, and operational protocols for ArangoDB within the Info-Geometry Spire.

## ⚖️ The Role of ArangoDB (Four Isolated Lanes)

Per [`src/igf/config/env_aliases.py`](../src/igf/config/env_aliases.py) and [`docs/CANONICAL_AGENT_PIPELINE.md`](CANONICAL_AGENT_PIPELINE.md), ArangoDB is separated into distinct physical/logical lanes (none of which replaces Lean kernel proof authority):

1. **LeanTrail / Declaration DAG (`:8530`, `infogeometry` & `darwin_commits`)**: Stores the validated graph of Lean 4 declarations, InfoTrees, overlays, and Darwin commit tracking (`ARANGO_*`, `DARWIN_ARANGO_*`). On this workstation, the legacy container `arango_alexandria` from `configs/alexandria/docker-compose.yml` occupies port `8530`.
2. **Hive Queue & aiClaw Memory (`:8540`, `hive_live` & `aiclaw_auto_rag`)**: Live Hive task/goal queue (`HIVE_ARANGO_*`) and natural-language proof memory (`AICLAW_ARANGO_*`).
3. **Alexandria PDF Literature Default (`:8532`, `alexandria`)**: Dedicated literature/PDF GraphRAG store (`ALEXANDRIA_ARANGO_*`, launched via [`configs/alexandria/docker-compose.pdf.yml`](../configs/alexandria/docker-compose.pdf.yml)). Carries `sourceAuthority: "retrieval_context_only"`.
4. **Dedicated Isolated Alexandria DAG Brains (e.g., observed `:8538`, `alexandria_dag_brain`)**: Spawned from `configs/alexandria/docker-compose.pdf.yml` with overridden `ALEXANDRIA_ARANGO_CONTAINER`, `ALEXANDRIA_ARANGO_PORT`, and `ALEXANDRIA_ARANGO_{DATA,APPS}_VOLUME`. `guard_alexandria_target()` enforces that Alexandria tools never touch `:8530` or `:8540` or non-Alexandria databases (`infogeometry`, `darwin_commits`, `hive_live`, `aiclaw_auto_rag`).

## 🛠️ Operational Lifecycle

### 1. Starting ArangoDB

- **Alexandria PDF-to-DAG-Brain Compose (Preferred for Alexandria)**: [`configs/alexandria/docker-compose.pdf.yml`](../configs/alexandria/docker-compose.pdf.yml)
  - Default `:8532` (`arango_alexandria_pdf`, DB `alexandria`):
    ```bash
    docker compose -f configs/alexandria/docker-compose.pdf.yml up -d
    ```
  - Dedicated isolated instance (for example `:8538` / `alexandria_dag_brain`):
    ```bash
    ALEXANDRIA_ARANGO_CONTAINER=arango_alexandria_dag \
    ALEXANDRIA_ARANGO_PORT=8538 \
    ALEXANDRIA_ARANGO_DATA_VOLUME=alexandria_dag_brain_data \
    ALEXANDRIA_ARANGO_APPS_VOLUME=alexandria_dag_brain_apps \
    docker compose -p alexandria_dag_brain -f configs/alexandria/docker-compose.pdf.yml up -d
    ```
  - See [`configs/alexandria/README.md`](../configs/alexandria/README.md) for environment precedence (`ALEXANDRIA_ARANGO_ENV_FILE`, `.env.example`) and credential hygiene.
- **Legacy Compose (`configs/alexandria/docker-compose.yml`)**: Pins `container_name: arango_alexandria`; on this workstation that container holds the `:8530` Lean DAG lane, so do **not** run it as the PDF Alexandria lane.

### 2. Ingestion and Rewriting (Data Flow)

- **Alexandria PDF-to-DAG-Brain Pipeline** (see [`tools/alexandria/README.md`](../tools/alexandria/README.md)):
  - Build JSONL + acyclic DAG (`alexandria_dag_edges`) and ingest directly or via two steps:
    ```bash
    python3 tools/alexandria/pdf_corpus_ingest.py \
      --input-dir /path/to/pdfs \
      --output-dir artifacts/alexandria_dag_brain \
      --exclude-default-noise --resume \
      --ingest-arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
      --replace-documents
    ```
  - Standalone JSONL import + BM25 `alexandria_chunks_search` view management:
    ```bash
    python3 tools/alexandria/arango_ingest.py \
      --input-dir artifacts/alexandria_dag_brain \
      --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
      --skip-unchanged
    ```
- **LeanTrail DAG (`:8530`, `infogeometry`)**: Hydrated from JSONL exports generated during the Lean build and DAG refresh process (`artifacts/leantrail/arango/ig_nodes.jsonl`, `ig_edges.jsonl`) using:
  ```bash
  python3 tools/leantrail/arango_ingest.py --drop-existing
  ```
  The `--drop-existing` flag truncates the collections before importing fresh data.

### 3. Recovery and Persistence
- **Persistence**: Managed via Docker volumes (`alexandria_arango_data` for `:8530`, `alexandria_pdf_arango_data` for `:8532`, or custom `ALEXANDRIA_ARANGO_DATA_VOLUME` for isolated Alexandria instances).
- **Recovery**: In case of volume loss, the LeanTrail DAG can be reconstructed by re-running the DAG refresh and ingestion pipeline, and Alexandria can be reconstructed from cached JSONL (`arango_ingest.py`) or raw PDFs (`pdf_corpus_ingest.py --resume`).

## 🧬 Key Scripts

| Script | Purpose |
|--------|---------|
| `tools/alexandria/pdf_corpus_ingest.py` | PDF inventory, SHA-256 dedup, chunk/archetype/DAG extraction, optional Ollama/`/v1` enrichment, and isolated ArangoDB ingestion. |
| `tools/alexandria/arango_ingest.py` | Stdlib HTTP Alexandria JSONL importer (`--replace-documents`, `--skip-unchanged`) + `alexandria_chunks_search` BM25 view builder. |
| `tools/alexandria/retrieve_context.py` | BM25 + `searchTerms` + 1-hop adjacent + 1..3-hop `alexandria_dag_edges` BFS retrieval (`--arango` or `--input-dir`). |
| `tools/alexandria/graph_context_rank.py` | NetworkX Personalized PageRank subgraph ranking across `adjacent`, `dag`/`dag_reverse`, `entity_relation`, and `canonicalKey` edges (requires `networkx`). |
| `tools/leantrail/arango_ingest.py` | Primary LeanTrail ingestion engine (supports `--drop-existing`). |
| `tools/infra/arango_gravity_context.py` | Generates LLM context packets from ArangoDB Lean DAG data. |
| `tools/infra/arango_fidelity_audit.py` | Verifies that ArangoDB state matches current Lean source. |
| `tools/leantrail/arango_physics_evaluator.py` | Evaluates information-geometric neighborhoods. |

## 🛡️ The Pauli Audit Gate
Closure is strictly forbidden if the target declaration carries "hypothesis debt" not reflected in the ArangoDB DAG. The `check_research_handoff_gate.py` script now integrates a debt check that queries these structures to enforce this mandate.
