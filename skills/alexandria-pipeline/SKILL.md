---
name: alexandria-pipeline
description: Digest PDF or LaTeX corpora into a dedicated Alexandria ArangoDB DAG-brain instance, run hybrid GraphRAG and Personalized PageRank retrieval across mathematical archetypes, or enrich chunks with Qwen3.8/vLLM or Ollama. Use when querying or ingesting literature in Alexandria (:8532 or :8538 alexandria_dag_brain) and mapping retrieved papers to Lean 4 owner modules.
metadata:
  short-description: Alexandria PDF/LaTeX GraphRAG pipeline & isolated DAG brain
---

<!-- repository-context-rule -->
## Repository context rule

For repository work, the current checked-out codebase is the context. Search
existing implementation and trace actual carriers, definitions, imports,
instances, theorem statements, and uses before claiming a structure is missing
or incorrect. A local absence is not a repository-wide absence. Names,
heuristics, summaries, and documentation guide discovery but do not override
source. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md` before repo-wide gap claims.

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Every Alexandria document, chunk, entity, and GraphRAG hit carries `sourceAuthority: "retrieval_context_only"` and is **NOT** verified Lean proof evidence. Descend from any literature hit to Lean owner files under `lean/InfoGeometry/` and validate with kernel checks.

# Alexandria Pipeline Operations

Canonical documentation:
- [`docs/alexandria/README.md`](../../docs/alexandria/README.md)
- [`docs/alexandria/ALEXANDRIA_SKILL.md`](../../docs/alexandria/ALEXANDRIA_SKILL.md)
- [`docs/alexandria/HYBRID_GRAPHRAG.md`](../../docs/alexandria/HYBRID_GRAPHRAG.md)
- [`tools/alexandria/README.md`](../../tools/alexandria/README.md)
- [`configs/alexandria/README.md`](../../configs/alexandria/README.md)

## 1. Strict Lane & Port Isolation

`guard_alexandria_target` ([`src/igf/config/env_aliases.py`](../../src/igf/config/env_aliases.py)) isolates Alexandria from the Lean AST/AQL declaration DAG and Hive lanes:
- **Forbidden ports:** `:8530` (Lean DAG `infogeometry` / `darwin_commits`) and `:8540` (Hive `hive_live` / `aiclaw_auto_rag`). CLIs exit with code `2` if pointed there.
- **Default Alexandria PDF target:** `http://127.0.0.1:8532` / database `alexandria` ([`configs/alexandria/docker-compose.pdf.yml`](../../configs/alexandria/docker-compose.pdf.yml)).
- **Dedicated PDF DAG-Brain target (observed active instance):** `http://127.0.0.1:8538` / database `alexandria_dag_brain` (container `arango_alexandria_dag`).
- **Env resolution order:** explicit CLI flags > exported `ALEXANDRIA_*` env vars > `ALEXANDRIA_ARANGO_ENV_FILE` (`configs/alexandria/.env`). Never print `.env` passwords.

## 2. Live & Offline Retrieval

- **BM25 + multi-hop acyclic DAG lookup (`retrieve_context.py`, stdlib `python3` or `.venv/bin/python3`):**
  ```bash
  .venv/bin/python3 tools/alexandria/retrieve_context.py \
    --arango \
    --endpoint http://127.0.0.1:8538 \
    --database alexandria_dag_brain \
    --query "Krein space fundamental symmetry Peirce decomposition" \
    --top-k 5 --hops 2 --format text
  ```

- **Cross-document Personalized PageRank (`graph_context_rank.py`, requires `networkx`):**
  > **Python environment note:** Bare `python3` in `PATH` may point to `OpenGauss/venv/bin/python3`, which lacks `networkx`. Use `.venv/bin/python3` or `/home/goutev/miniforge3/envs/sage/bin/python`.

  ```bash
  .venv/bin/python3 tools/alexandria/graph_context_rank.py \
    --arango \
    --endpoint http://127.0.0.1:8538 \
    --database alexandria_dag_brain \
    --query "Drazin inverse Riesz projector spectral decomposition" \
    --top-k 5 --seed-k 5 --hops 2 --format text
  ```

- **Unified Repo Explorer (`ask_repo.py` / `graph_rag_query.py`, opt-in `--scope alexandria`):**
  Alexandria is intentionally excluded from `--scope all`. Request it explicitly:
  ```bash
  python3 tools/infra/ask_repo.py "Krein space fundamental symmetry Peirce decomposition" \
    --scope alexandria \
    --alexandria-endpoint http://127.0.0.1:8538 \
    --alexandria-database alexandria_dag_brain \
    --top-k 5 --brief
  ```

For offline JSONL retrieval without ArangoDB, swap `--arango --endpoint ... --database ...` for `--input-dir artifacts/alexandria_dag_brain`.

## 3. Dedicated Container Deployment & Corpus Ingestion

1. **Start an isolated container** using [`configs/alexandria/docker-compose.pdf.yml`](../../configs/alexandria/docker-compose.pdf.yml) (avoid legacy `configs/alexandria/docker-compose.yml`, whose `arango_alexandria` name collides with the `:8530` Lean DAG container on this host):
   ```bash
   ALEXANDRIA_ARANGO_CONTAINER=arango_alexandria_dag \
   ALEXANDRIA_ARANGO_PORT=8538 \
   ALEXANDRIA_ARANGO_DATA_VOLUME=alexandria_dag_brain_data \
   ALEXANDRIA_ARANGO_APPS_VOLUME=alexandria_dag_brain_apps \
   docker compose -p alexandria_dag_brain -f configs/alexandria/docker-compose.pdf.yml up -d
   ```

2. **Ingest PDF corpus -> JSONL + acyclic DAG + ArangoDB:**
   ```bash
   python3 tools/alexandria/pdf_corpus_ingest.py \
     --input-dir /home/goutev/Downloads/collection_for_formalization \
     --output-dir artifacts/alexandria_dag_brain \
     --exclude-default-noise --resume --workers 4 \
     --ingest-arango \
     --endpoint http://127.0.0.1:8538 \
     --database alexandria_dag_brain \
     --skip-unchanged
   ```
   - Use `--replace-documents` instead of `--skip-unchanged` to purge and reload modified document chunks/entities/edges.
   - For bounded LLM enrichment against `/v1` (e.g., Qwen3.8 27B NVFP4) or Ollama, add `--enrich-ollama --ollama-endpoint http://127.0.0.1:8000/v1 --ollama-model Qwen/Qwen3.8-27B-NVFP4 --enrich-ollama-workers 8 --enrich-ollama-max-tokens 1024 --enrich-ollama-max-chunks 200` (`enable_thinking: false` is sent by default on `/v1`; pass `--allow-thinking` to opt in; bearer auth uses `--enrich-ollama-api-key` or `ALEXANDRIA_LLM_API_KEY` / `OPENAI_API_KEY`).

## 4. Blueprint Mapping & Offline Tests

- Map Alexandria theorem/definition chunks against local Lean search records (`blueprint_alexandria_bridge.py` takes `--out`):
  ```bash
  python3 tools/infra/blueprint_alexandria_bridge.py \
    --input-dir artifacts/alexandria_dag_brain \
    --out artifacts/alexandria_dag_brain/blueprint_nodes.jsonl
  ```
- Run the offline unit suite (using an env with `pytest`, `pypdf`, `networkx`):
  ```bash
  PYTHONDONTWRITEBYTECODE=1 /home/goutev/miniforge3/envs/sage/bin/python -m pytest -p no:cacheprovider -v \
    tests/alexandria tests/test_arango_env.py
  ```
- 5-tier E2E suite ([`tests/e2e_alexandria_pdf/`](../../tests/e2e_alexandria_pdf/)): exercises ephemeral test DBs on `:8532` and refuses `:8530`/`:8540` and protected DBs (`alexandria`, `infogeometry`, `darwin_commits`, `hive_live`, `aiclaw_auto_rag`).
