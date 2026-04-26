# ArangoDB Management and Architecture

This document defines the role, lifecycle, and operational protocols for ArangoDB within the Info-Geometry Spire.

## ⚖️ The Role of ArangoDB (The Authoritative Lane)

Per the **Pauli Auditor Protocol**, ArangoDB acts as the **Multi-Model Authoritative Lane** for all formal knowledge that has passed the initial "Jungian" (exploratory) phase.

1.  **LeanTrail DAG**: Stores the validated graph of Lean 4 declarations, types, and proofs.
2.  **Alexandria**: Stores the broader knowledge base, including physics-of-information formalizations and cross-representation mappings.
3.  **Gravitational Context**: Provides the retrieval substrate for LLM agents to find relevant proven theorems during proof search.

## 🛠️ Operational Lifecycle

### 1. Starting ArangoDB
ArangoDB is containerized via Docker.

- **Primary Configuration**: `configs/alexandria/docker-compose.yml`
- **Start Command**:
  ```bash
  docker compose -f configs/alexandria/docker-compose.yml up -d
  ```
- **Port**: Exposed on `8530` (internal 8529).
- **Credentials**: Root password defaults to `alexandria_root` (configurable via `.env`).

### 2. Ingestion and Rewriting (Data Flow)
The database is hydrated from **JSONL exports** generated during the Lean build and DAG refresh process.

- **Source Artifacts**: `artifacts/leantrail/arango/ig_nodes.jsonl`, `ig_edges.jsonl`
- **Ingestion Script**: `tools/leantrail/arango_ingest.py`
- **Rewrite Protocol**: To perform a full rewrite (recovery) of the database:
  ```bash
  python3 tools/leantrail/arango_ingest.py --drop-existing
  ```
  The `--drop-existing` flag truncates the collections before importing fresh data.

### 3. Recovery and Persistence
- **Persistence**: Managed via Docker volumes (`alexandria_arango_data`).
- **Recovery**: In case of volume loss, the database can be perfectly reconstructed by re-running the full DAG refresh and ingestion pipeline.

## 🧬 Key Scripts

| Script | Purpose |
|--------|---------|
| `tools/leantrail/arango_ingest.py` | Primary ingestion engine (supports `--drop-existing`). |
| `tools/infra/arango_gravity_context.py` | Generates LLM context packets from ArangoDB data. |
| `tools/infra/arango_fidelity_audit.py` | Verifies that ArangoDB state matches current Lean source. |
| `tools/leantrail/arango_physics_evaluator.py` | Evaluates information-geometric neighborhoods. |

## 🛡️ The Pauli Audit Gate
Closure is strictly forbidden if the target declaration carries "hypothesis debt" not reflected in the ArangoDB DAG. The `check_research_handoff_gate.py` script now integrates a debt check that queries these structures to enforce this mandate.
