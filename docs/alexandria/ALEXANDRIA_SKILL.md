# Alexandria Skill Guide (Agent Workflow)

Use Alexandria when a Lean 4 formalization task, mathematical design review, or proof search needs literature definitions, theorem statements, archetype analogs across papers, or structural provenance from the PDF/LaTeX corpus. See also [docs/alexandria/README.md](README.md), [tools/alexandria/README.md](../../tools/alexandria/README.md), [configs/alexandria/README.md](../../configs/alexandria/README.md), and [skills/alexandria-pipeline/SKILL.md](../../skills/alexandria-pipeline/SKILL.md).

> **Authority rule:** All Alexandria hits carry `sourceAuthority: "retrieval_context_only"`. Never cite an Alexandria hit as Lean proof evidence. Always verify candidate definitions and theorem statements in the source `.lean` owner files using `tools/infra/run_locked_lean.py`, `tools/infra/run_locked_lake_build.py`, and `axiom_check.lean`.

---

## 1. Safety & Port Guardrails

`guard_alexandria_target` (`src/igf/config/env_aliases.py`) isolates Alexandria from Lean AST/DAG and Hive instances:
- **Never target** port `8530` (database `infogeometry`, `darwin_commits`) or port `8540` (database `hive_live`).
- **Default Alexandria target:** `http://127.0.0.1:8532`, database `alexandria`.
- **Dedicated PDF DAG-Brain target (recommended when active):** `http://127.0.0.1:8538`, database `alexandria_dag_brain` (container `arango_alexandria_dag`).

Check active containers before running live Arango queries:
```bash
docker ps --format "table {{.Names}}\t{{.Ports}}\t{{.Status}}"
```

---

## 2. Querying the Live PDF DAG-Brain (`:8538` / `alexandria_dag_brain`)

### Fast BM25 + Acyclic DAG Expansion (`retrieve_context.py`)
```bash
python3 tools/alexandria/retrieve_context.py \
  --arango \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --query "Krein space fundamental symmetry Peirce decomposition" \
  --top-k 8 \
  --hops 2 \
  --format text
```

### Cross-Document Personalized PageRank (`graph_context_rank.py`)
Use this when you want cross-paper conceptual bridging via `canonicalKey`, `math_archetype` co-occurrence, `entity_relation` edges, and multi-hop DAG propagation (`graph_context_rank.py` requires `networkx`; use `.venv/bin/python3` or `/home/goutev/miniforge3/envs/sage/bin/python` rather than a bare `python3` lacking `networkx`):
```bash
.venv/bin/python3 tools/alexandria/graph_context_rank.py \
  --arango \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --query "Krein-Hilbert majorant commutator uncertainty inequality" \
  --seed-k 6 \
  --top-k 10 \
  --hops 2 \
  --format text
```
Add `--json-out artifacts/alexandria_query.json --format json` when downstream scripts need structured provenance (`documentKey`, `contentHash`, `pageStart`, `pageEnd`, `entities`, `dagNeighbors`).

### Unified Repo GraphRAG Explorer (`ask_repo.py` / `graph_rag_query.py`)
Alexandria is opt-in via `--scope alexandria` (it is intentionally excluded from `--scope all`):
```bash
python3 tools/infra/ask_repo.py "Krein space fundamental symmetry Peirce decomposition" \
  --scope alexandria \
  --alexandria-endpoint http://127.0.0.1:8538 \
  --alexandria-database alexandria_dag_brain \
  --top-k 5 --brief
```

### Offline Fallback (JSONL Artifacts Without ArangoDB)
```bash
.venv/bin/python3 tools/alexandria/graph_context_rank.py \
  --input-dir artifacts/alexandria_dag_brain \
  --query "multiple Peirce decomposition idempotent" \
  --top-k 8 \
  --format text
```

---

## 3. Digesting or Updating a PDF Corpus (`pdf_corpus_ingest.py`)

### Starting an Isolated ArangoDB Instance on Custom Port (`docker-compose.pdf.yml`)
Set `ALEXANDRIA_ARANGO_PASSWORD` in local env or `configs/alexandria/.env` without echoing secrets:
```bash
ALEXANDRIA_ARANGO_CONTAINER=arango_alexandria_dag \
ALEXANDRIA_ARANGO_PORT=8538 \
ALEXANDRIA_ARANGO_DATA_VOLUME=alexandria_dag_brain_data \
ALEXANDRIA_ARANGO_APPS_VOLUME=alexandria_dag_brain_apps \
docker compose -p alexandria_dag_brain -f configs/alexandria/docker-compose.pdf.yml up -d
```

### Deterministic PDF Extraction + DAG Verification + ArangoDB Load
```bash
python3 tools/alexandria/pdf_corpus_ingest.py \
  --input-dir /home/goutev/Downloads/collection_for_formalization \
  --output-dir artifacts/alexandria_dag_brain \
  --exclude-default-noise \
  --resume \
  --workers 4 \
  --ingest-arango \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --skip-unchanged
```
Key operational flags on `tools/alexandria/pdf_corpus_ingest.py`:
- `--exclude-default-noise`: skips known non-paper manuals/assets (`*Isabelle2025*`, `*Act_Content*`, `*OV2640_DS*`, `*JFETS_The_New_Frontier*`); add `--exclude-glob "<pattern>"` for extra exclusions.
- `--resume`: caches per-PDF extracted packets in `<output-dir>/.doc_cache` so interrupted runs resume without re-running `pdftotext`.
- `--replace-documents` vs `--skip-unchanged`: `--replace-documents` purges stale sections/chunks/entities/edges per document before re-import; `--skip-unchanged` skips documents with matching `contentHash`.
- Inspect `corpus_inventory_report.json` / `corpus_inventory_report.md` in `--output-dir` for SHA-256 deduplication counts, `outcome_counts`, `chunk_kind_counts`, `dag_edge_type_counts`, and `dag_edges_pruned_for_cycles`.

### Optional Qwen3.8 27B NVFP4 (`/v1`) or Ollama Enrichment
When an OpenAI-compatible vLLM `/v1` server (such as `eugr/spark-vllm:nightly-20261002` with Qwen3.8 27B NVFP4) or Ollama server is running:
```bash
python3 tools/alexandria/pdf_corpus_ingest.py \
  --input-dir /home/goutev/Downloads/collection_for_formalization \
  --output-dir artifacts/alexandria_dag_brain \
  --exclude-default-noise \
  --resume \
  --workers 4 \
  --enrich-ollama \
  --ollama-endpoint http://127.0.0.1:8000/v1 \
  --ollama-model Qwen/Qwen3.8-27B-NVFP4 \
  --enrich-ollama-workers 8 \
  --enrich-ollama-max-tokens 1024 \
  --enrich-ollama-max-chunks 200
```
- `/v1` endpoints automatically probe `<endpoint>/models`, call `<endpoint>/chat/completions` with `response_format: {"type": "json_object"}`, and disable thinking tokens by default via `chat_template_kwargs: {"enable_thinking": false}` (override with `--allow-thinking`).
- Pass `--enrich-ollama-api-key` or set `ALEXANDRIA_LLM_API_KEY` / `OPENAI_API_KEY` if the endpoint requires bearer authentication.

---

## 4. Ingesting LaTeX Papers, Markdown, or Local Files

- **arXiv / `.tex` / Markdown papers:**
  ```bash
  python3 tools/alexandria/math_paper_graphrag_ingest.py \
    --input /path/to/paper.tex \
    --output artifacts/alexandria/latex_run && \
  python3 tools/alexandria/arango_ingest.py \
    --input-dir artifacts/alexandria/latex_run \
    --endpoint http://127.0.0.1:8538 \
    --database alexandria_dag_brain \
    --replace-documents
  ```
- **Plain Markdown / `.txt` / `.lean` notes:** `tools/alexandria/semantic_ingest.py` -> `tools/alexandria/arango_ingest.py`.

---

## 5. Mathematical Archetypes & Lean 4 Owner Handoff

`pdf_corpus_ingest.py` tags chunks with up to 10 `math_archetype` entities carrying cross-document `canonicalKey` values:
`z2_graded_polarization`, `curved_dga_differential`, `clifford_spinor_tower`, `krein_indefinite_metric`, `drazin_riesz_spectral`, `souriau_metriplectic_thermo`, `modular_kms_monodromy`, `categorical_colimit_tower`, `noncommutative_k_theory`, `yang_mills_gauge_holonomy`.

To connect retrieved theorem/definition chunks to candidate Lean declarations:
```bash
python3 tools/infra/blueprint_alexandria_bridge.py \
  --input-dir artifacts/alexandria_dag_brain \
  --out artifacts/alexandria_dag_brain/blueprint_nodes.jsonl
```
Then inspect the target Lean owner files directly (`AGENTS.md` mathematical acceptance rules), formalize theorem-by-theorem with no `sorry`/`admit`/axioms, and verify via:
```bash
python3 tools/infra/opengauss_screener.py <owner.lean>
python3 tools/infra/run_locked_lean.py --wait-for-build-lock <owner.lean> -- -DwarningAsError=true
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <InfoGeometry.Module>
flock -x /tmp/info-geometry-build.lock lake env lean --run tools/infra/axiom_check.lean <.lake/build/lib/lean/.../Module.olean>
```

---

## 6. Offline Pipeline Self-Test

```bash
PYTHONDONTWRITEBYTECODE=1 /home/goutev/miniforge3/envs/sage/bin/python -m pytest -p no:cacheprovider -v \
  tests/alexandria tests/test_arango_env.py
```

---

## 7. Operational Lessons (DAG Audit Integration & Live `:8538` GraphRAG)

- **Verify the execution environment alongside DAG audits:** When using repo-native Alexandria alongside the DAG audit, verify the active Python/ArangoDB environment before claiming a full semantic-ingest or live Arango run. Port `8530` (`infogeometry`) is the core Lean DAG lane and is forbidden for Alexandria by `guard_alexandria_target`. When live Alexandria-Arango is unavailable, use local JSONL digest/ranking (`--input-dir`) and report explicitly that live Alexandria-Arango querying was not performed.
- **Live Alexandria GraphRAG target (`:8538` / `alexandria_dag_brain`):** The documented operational target is `http://127.0.0.1:8538` with database `alexandria_dag_brain`. Use `.venv/bin/python3` (the repo venv with `networkx` and `python-arango`, or `/home/goutev/miniforge3/envs/sage/bin/python`) and pass the explicit `--arango` flag (without `--arango`, the CLIs read local JSONL via `--input-dir`).
- **Verified baseline queries (`authority = retrieval_context_only`):**
  - `retrieve_context.py --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain --query "Krein space fundamental symmetry Peirce decomposition" --top-k 5 --hops 2 --format text` returned `5` BM25 hits (`59.78`–`65.76`) across `2103.04372v1.pdf`, `mccrimmon_jordan.pdf`, and `0110001v2.pdf`.
  - `graph_context_rank.py --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain --query "Drazin inverse Riesz projector spectral decomposition" --top-k 5 --hops 2 --format text` built a `35`-node / `702`-edge subgraph and returned `5` PageRank hits (top `0.0634`).
  - Both packets declare `authority = retrieval_context_only`: use them for source-discovery navigation, never as Lean proof evidence.
