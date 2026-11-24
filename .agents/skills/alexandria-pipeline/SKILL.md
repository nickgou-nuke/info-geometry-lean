---
name: alexandria-pipeline
description: Digest PDF or LaTeX corpora into a dedicated Alexandria ArangoDB DAG-brain instance, run hybrid GraphRAG and Personalized PageRank retrieval across mathematical archetypes, or enrich chunks with Qwen3.8/vLLM or Ollama. Use when querying or ingesting literature in Alexandria (:8532 or :8538 alexandria_dag_brain) and mapping retrieved papers to Lean 4 owner modules.
metadata:
  short-description: Operate the Alexandria PDF/LaTeX GraphRAG pipeline
---

# Alexandria Pipeline Operations

Follow [docs/alexandria/README.md](../../../docs/alexandria/README.md),
[docs/alexandria/ALEXANDRIA_SKILL.md](../../../docs/alexandria/ALEXANDRIA_SKILL.md),
[docs/alexandria/HYBRID_GRAPHRAG.md](../../../docs/alexandria/HYBRID_GRAPHRAG.md),
[tools/alexandria/README.md](../../../tools/alexandria/README.md),
[configs/alexandria/README.md](../../../configs/alexandria/README.md), and
[skills/alexandria-pipeline/SKILL.md](../../../skills/alexandria-pipeline/SKILL.md)
for the full schema, archetype taxonomy, lane isolation, and retrieval commands.

> **Authority boundary:** Alexandria hits carry `sourceAuthority: "retrieval_context_only"`.
> Never present retrieved PDF/LaTeX chunks as Lean proof evidence or mathematical truth.
> Always inspect and kernel-verify actual `.lean` owner modules.

## 1. Strict Lane & Port Isolation

`guard_alexandria_target` (`src/igf/config/env_aliases.py`) blocks non-Alexandria targets:
- **Forbidden ports:** `:8530` (Lean AST/AQL declaration DAG) and `:8540` (Hive).
- **Forbidden databases:** `infogeometry`, `darwin_commits`, `hive_live`, `aiclaw_auto_rag`.
- **Default Alexandria port/database:** `http://127.0.0.1:8532` / `alexandria`.
- **Dedicated PDF DAG-Brain port/database (when active):** `http://127.0.0.1:8538` / `alexandria_dag_brain` (container `arango_alexandria_dag`).

Check container state first:
```bash
docker ps --format "table {{.Names}}\t{{.Ports}}\t{{.Status}}"
```

## 2. Query Live PDF DAG-Brain (`:8538` / `alexandria_dag_brain`)

- **BM25 + DAG neighborhood lookup (`retrieve_context.py`):**
  ```bash
  python3 tools/alexandria/retrieve_context.py \
    --arango \
    --endpoint http://127.0.0.1:8538 \
    --database alexandria_dag_brain \
    --query "<mathematical query>" \
    --top-k 8 \
    --hops 2 \
    --format text
  ```

- **Cross-document Personalized PageRank (`graph_context_rank.py`, requires `networkx`):**
  Use `.venv/bin/python3` or `/home/goutev/miniforge3/envs/sage/bin/python` (bare `python3` in `PATH` may lack `networkx`):
  ```bash
  .venv/bin/python3 tools/alexandria/graph_context_rank.py \
    --arango \
    --endpoint http://127.0.0.1:8538 \
    --database alexandria_dag_brain \
    --query "<archetype or theorem query>" \
    --seed-k 6 \
    --top-k 10 \
    --hops 2 \
    --format text
  ```

- **Unified Repo Explorer (`ask_repo.py` / `graph_rag_query.py`, opt-in `--scope alexandria`, excluded from `--scope all`):**
  ```bash
  python3 tools/infra/ask_repo.py "<query>" \
    --scope alexandria \
    --alexandria-endpoint http://127.0.0.1:8538 \
    --alexandria-database alexandria_dag_brain \
    --top-k 5 --brief
  ```

For offline JSONL queries without ArangoDB, swap `--arango --endpoint ... --database ...` for `--input-dir artifacts/alexandria_dag_brain`.

## 3. Start Dedicated Container & Ingest PDF Corpus

Start an isolated PDF DAG-brain instance on a dedicated port via `configs/alexandria/docker-compose.pdf.yml` (set `ALEXANDRIA_ARANGO_PASSWORD` via local `.env` or shell environment without echoing secrets):
```bash
ALEXANDRIA_ARANGO_CONTAINER=arango_alexandria_dag \
ALEXANDRIA_ARANGO_PORT=8538 \
ALEXANDRIA_ARANGO_DATA_VOLUME=alexandria_dag_brain_data \
ALEXANDRIA_ARANGO_APPS_VOLUME=alexandria_dag_brain_apps \
docker compose -p alexandria_dag_brain -f configs/alexandria/docker-compose.pdf.yml up -d
```

Run resilient SHA-256 deduplicated ingestion, noise exclusion, acyclic DAG pruning, and ArangoDB upload:
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

To enable OpenAI-compatible `/v1` semantic enrichment (e.g. Qwen3.8 27B NVFP4 on `eugr/spark-vllm:nightly-20261002`), add:
```bash
  --enrich-ollama \
  --ollama-endpoint http://127.0.0.1:8000/v1 \
  --ollama-model Qwen/Qwen3.8-27B-NVFP4 \
  --enrich-ollama-workers 8 \
  --enrich-ollama-max-tokens 1024 \
  --enrich-ollama-max-chunks 200
```
Pass `--allow-thinking` only if you want reasoning tokens enabled (`chat_template_kwargs: {"enable_thinking": false}` is sent by default on `/v1`). Bearer auth uses `--enrich-ollama-api-key` or `ALEXANDRIA_LLM_API_KEY` / `OPENAI_API_KEY`.

## 4. Blueprint Bridge & Tests

- Map Alexandria theorem/definition chunks to local Lean search hits:
  ```bash
  python3 tools/infra/blueprint_alexandria_bridge.py \
    --input-dir artifacts/alexandria_dag_brain \
    --out artifacts/alexandria_dag_brain/blueprint_nodes.jsonl
  ```
- Run the offline Alexandria + env-isolation test suite:
  ```bash
  PYTHONDONTWRITEBYTECODE=1 /home/goutev/miniforge3/envs/sage/bin/python -m pytest -p no:cacheprovider -v \
    tests/alexandria tests/test_arango_env.py
  ```

## 5. Operational Lessons (DAG Audit Integration & Live `:8538` GraphRAG)

- **DAG Audit & Environment Verification:** When using repo-native Alexandria alongside the DAG audit, verify the execution environment before claiming a full semantic-ingest or live Arango run. Port `8530` is the core Lean DAG lane (`infogeometry`) and is forbidden for Alexandria; if live Alexandria-Arango is unavailable, fall back to local JSONL digest/ranking (`--input-dir`) and explicitly report that live Alexandria-Arango querying was not performed.
- **Live Alexandria GraphRAG Target (`:8538` / `alexandria_dag_brain`):** Use `.venv/bin/python3` (or `/home/goutev/miniforge3/envs/sage/bin/python`, which provide `networkx` and `python-arango`) and pass `--arango` explicitly (without `--arango`, the CLIs read local JSONL). Verified baseline runs:
  - `retrieve_context.py --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain --query "Krein space fundamental symmetry Peirce decomposition" --top-k 5 --hops 2 --format text` → `5` BM25 hits (`59.78`–`65.76`) across `2103.04372v1.pdf`, `mccrimmon_jordan.pdf`, and `0110001v2.pdf`.
  - `graph_context_rank.py --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain --query "Drazin inverse Riesz projector spectral decomposition" --top-k 5 --hops 2 --format text` → `35`-node / `702`-edge subgraph, `5` PageRank hits (top `0.0634`).
  - Both packets declare `authority = retrieval_context_only`: source-discovery navigation only, never Lean proof evidence.
