# Alexandria Pipeline — Literature & Mathematical Archetypes GraphRAG

> **Authority boundary:** Records produced and retrieved by Alexandria carry `sourceAuthority: "retrieval_context_only"` and exist strictly for literature navigation, theorem discovery, and mathematical-archetype linking. They are **never** Lean proof evidence or mathematical truth. Kernel-checked `.lean` owners and `axiom_check.lean` remain the sole authority for formalized claims.

Alexandria is the repository's isolated literature and mathematical-knowledge pipeline. It ingests PDF libraries, LaTeX/arXiv papers, Markdown books, and source notes into JSONL graph artifacts and a dedicated ArangoDB 3.12 instance with BM25 search (`alexandria_chunks_search`), typed acyclic DAG edges (`alexandria_dag_edges`), mathematical archetype entities (`math_archetype` with cross-document `canonicalKey`), and Personalized PageRank retrieval.

---

## 1. Lane Isolation & Dedicated ArangoDB Instances

Alexandria **must never** write into or target the Lean AST/AQL declaration DAG (`:8530`, database `infogeometry`), Darwin commits (`darwin_commits`), or Hive live state (`:8540`, database `hive_live`). `guard_alexandria_target` in `src/igf/config/env_aliases.py` enforces this boundary across CLI tools and raises an error on forbidden ports (`8530`, `8540`) or forbidden databases (`infogeometry`, `darwin_commits`, `hive_live`, `aiclaw_auto_rag`).

### Environment Resolution Order
1. Explicit CLI flags: `--endpoint`, `--database`, `--username`, `--password`
2. Process environment variables: `ALEXANDRIA_ARANGO_ENDPOINT`, `ALEXANDRIA_ARANGO_PORT`, `ALEXANDRIA_ARANGO_DB` (or `ALEXANDRIA_ARANGO_DATABASE`), `ALEXANDRIA_ARANGO_USERNAME` / `ALEXANDRIA_ARANGO_USER`, `ALEXANDRIA_ARANGO_PASSWORD` / `ALEXANDRIA_ARANGO_PASS`
3. Repo-local env file `configs/alexandria/.env` (template at `configs/alexandria/.env.example`), defaulting to `http://127.0.0.1:8532` and database `alexandria`.

### Starting a Dedicated ArangoDB Instance

Use [`configs/alexandria/docker-compose.pdf.yml`](../../configs/alexandria/docker-compose.pdf.yml) for Alexandria PDF/DAG-brain deployments (avoid legacy [`configs/alexandria/docker-compose.yml`](../../configs/alexandria/docker-compose.yml), whose `container_name: arango_alexandria` holds the `:8530` Lean DAG container on this workstation):

- **Default Alexandria PDF container (port `8532`, DB `alexandria`):**
  ```bash
  cp -n configs/alexandria/.env.example configs/alexandria/.env
  docker compose -f configs/alexandria/docker-compose.pdf.yml up -d
  ```

- **Parameterized PDF DAG-Brain container (custom port, container, and named volumes):**
  `configs/alexandria/docker-compose.pdf.yml` parameterizes `ALEXANDRIA_ARANGO_CONTAINER`, `ALEXANDRIA_ARANGO_PORT`, `ALEXANDRIA_ARANGO_PASSWORD`, `ALEXANDRIA_ARANGO_DATA_VOLUME`, and `ALEXANDRIA_ARANGO_APPS_VOLUME`. For example, to run a dedicated PDF DAG-brain instance on port `8538` with database `alexandria_dag_brain` (supply `ALEXANDRIA_ARANGO_PASSWORD` in local env or `.env` without echoing secrets):
  ```bash
  ALEXANDRIA_ARANGO_CONTAINER=arango_alexandria_dag \
  ALEXANDRIA_ARANGO_PORT=8538 \
  ALEXANDRIA_ARANGO_DATA_VOLUME=alexandria_dag_brain_data \
  ALEXANDRIA_ARANGO_APPS_VOLUME=alexandria_dag_brain_apps \
  docker compose -p alexandria_dag_brain -f configs/alexandria/docker-compose.pdf.yml up -d
  ```

Verify readiness before ingesting or querying:
```bash
curl -s -o /dev/null -w "HTTP %{http_code}\n" http://127.0.0.1:8538/_api/version
```

---

## 2. PDF Corpus DAG-Brain Pipeline (`pdf_corpus_ingest.py`)

`tools/alexandria/pdf_corpus_ingest.py` builds a deduplicated, structurally chunked, archetype-tagged, cycle-free DAG brain from large PDF collections:

1. **Inventory & SHA-256 Deduplication:** Scans `--input-dir` recursively (skipping symlinks), detects `%PDF-` magic headers, deduplicates identical files by SHA-256, and skips noise files when `--exclude-default-noise` (`*Isabelle2025*`, `*Act_Content*`, `*OV2640_DS*`, `*JFETS_The_New_Frontier*`) or repeatable `--exclude-glob` patterns are provided.
2. **Resilient Extraction & Outcome Classification:** Uses `pdftotext -enc UTF-8` with `pypdf` fallback and `--per-file-timeout` protection. Every unique SHA-256 PDF receives an explicit outcome in `corpus_inventory_report.json` / `corpus_inventory_report.md`: `ingested`, `duplicate_skipped`, `empty_0_bytes`, `scanned_no_text`, `encrypted_no_text`, `very_low_text_skipped`, `parse_error`, or `limit_skipped`. Use `--resume` to cache per-document extractions under `<output-dir>/.doc_cache`.
3. **Structural Chunking:** Splits papers into typed chunks (`abstract`, `theorem`, `proof`, `definition`, `equation`, `remark`, `bibliography`, `prose`, etc.) with page provenance (`pageStart`, `pageEnd`) and token normalization.
4. **Mathematical Archetypes & Cross-Document `canonicalKey`:** Extracts entities and classifies chunks against 10 core `math_archetype` patterns (`MATH_ARCHETYPE_PATTERNS`):
   - `z2_graded_polarization`
   - `curved_dga_differential`
   - `clifford_spinor_tower`
   - `krein_indefinite_metric`
   - `drazin_riesz_spectral`
   - `souriau_metriplectic_thermo`
   - `modular_kms_monodromy`
   - `categorical_colimit_tower`
   - `noncommutative_k_theory`
   - `yang_mills_gauge_holonomy`

   Cross-document entity types receive deterministic `canonicalKey` hashes (`stable_key("concept", entity_type, norm)`), while local-only identifiers (`math_label`, `math_reference`, `bib_entry`) keep `canonicalKey: ""` so citations and labels do not falsely bridge unrelated papers.
5. **Strictly Acyclic DAG Edges (`alexandria_dag_edges`):** Emits 6 directed edge types (`DAG_EDGE_TYPES`):
   - `section_precedes_section`
   - `proof_proves_theorem`
   - `chunk_cites_entry`
   - `chunk_uses_definition`
   - `chunk_references_result`
   - `document_cites_document`

   `verify_and_prune_dag` enforces strict acyclicity by priority order (`DAG_EDGE_PRIORITY`) and runs an independent Kahn topological sort check.

### Running Full PDF Digestion + ArangoDB Import
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
  --replace-documents
```

To import pre-generated JSONL artifacts separately with incremental skip or clean document replacement:
```bash
python3 tools/alexandria/arango_ingest.py \
  --input-dir artifacts/alexandria_dag_brain \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --skip-unchanged
```

---

## 3. Optional LLM Semantic Enrichment (vLLM `/v1` Qwen3.8 27B NVFP4 or Ollama)

`pdf_corpus_ingest.py --enrich-ollama` supports both OpenAI-compatible `/v1` endpoints (e.g., `eugr/spark-vllm:nightly-20261002` serving Qwen3.8 27B NVFP4) and native Ollama endpoints:

- Endpoints ending in `/v1` probe `GET <endpoint>/models` and call `POST <endpoint>/chat/completions` with `response_format: {"type": "json_object"}`.
- By default, `--enrich-ollama` sends `"chat_template_kwargs": {"enable_thinking": false}` on `/v1` endpoints so structured JSON extraction is fast and bounded; pass `--allow-thinking` to permit chain-of-thought reasoning tokens.
- Non-`/v1` endpoints probe `/api/tags` and call `/api/chat`.

Example using a local vLLM `/v1` server (such as `eugr/spark-vllm:nightly-20261002` with Qwen3.8 27B NVFP4):
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
  --enrich-ollama-max-chunks 200 \
  --ingest-arango \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --skip-unchanged
```

Optional API bearer auth can be passed via `--enrich-ollama-api-key` or `ALEXANDRIA_LLM_API_KEY` / `OPENAI_API_KEY`.

---

## 4. Additional Text, Markdown, and LaTeX Ingestion Pipelines

- **LaTeX / arXiv / Math Markdown papers:** `tools/alexandria/math_paper_graphrag_ingest.py` chunks around LaTeX sections and unbroken `theorem`/`proof`/`equation`/`align` environments (never splitting inside environments), and optionally merges theorem blocks with following proofs:
  ```bash
  python3 tools/alexandria/math_paper_graphrag_ingest.py \
    --arxiv-id 2401.00001 \
    --output artifacts/alexandria/math_papers/2401_00001
  ```
- **Repository Markdown, docs, `.lean`, and Black Books prose:** `tools/alexandria/semantic_ingest.py`:
  ```bash
  python3 tools/alexandria/semantic_ingest.py \
    --input docs/ \
    --output artifacts/alexandria/docs_run
  ```

Both emit Alexandria JSONL collections compatible with `tools/alexandria/arango_ingest.py`.

---

## 5. ArangoDB Collections & Search View

`tools/alexandria/arango_ingest.py` ensures 4 document collections, 6 edge collections, secondary indexes, and 1 ArangoSearch view:

- **Document collections:** `alexandria_documents`, `alexandria_sections`, `alexandria_chunks`, `alexandria_entities`
- **Edge collections:**
  - `alexandria_document_section_edges`
  - `alexandria_section_chunk_edges`
  - `alexandria_chunk_entity_edges`
  - `alexandria_chunk_adjacent_edges`
  - `alexandria_entity_relation_edges`
  - `alexandria_dag_edges`
- **Search view:** `alexandria_chunks_search` (BM25 over `text` and `2.0x`-boosted `title` with `text_en` analyzer, plus exact matching on `searchTerms`).

---

## 6. Hybrid GraphRAG Retrieval & Personalized PageRank

- **Direct BM25 + Adjacent + DAG retrieval (`retrieve_context.py`):**
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

- **Graph-expanded Personalized PageRank (`graph_context_rank.py`):**
  Builds a directed graph up to 200 chunks combining adjacent chunks, directed `alexandria_dag_edges`, `entity_relation` edges, de Bruijn token sequences, and cross-document `shared_entity` edges linked by `canonicalKey` (with optional `--use-gpu` preferring NetworkX `cugraph` backend and automatic NetworkX fallback). Requires `networkx` — use `.venv/bin/python3` or `/home/goutev/miniforge3/envs/sage/bin/python` (bare `python3` in `PATH` may lack `networkx`):
  ```bash
  .venv/bin/python3 tools/alexandria/graph_context_rank.py \
    --arango \
    --endpoint http://127.0.0.1:8538 \
    --database alexandria_dag_brain \
    --query "multiple Peirce decomposition Jordan algebra idempotents" \
    --seed-k 6 \
    --top-k 8 \
    --hops 2 \
    --format text
  ```

- **Unified Repo Explorer (`ask_repo.py` / `graph_rag_query.py`, opt-in `--scope alexandria`):**
  Alexandria is excluded from `--scope all`. Request it explicitly:
  ```bash
  python3 tools/infra/ask_repo.py "Krein space fundamental symmetry Peirce decomposition" \
    --scope alexandria \
    --alexandria-endpoint http://127.0.0.1:8538 \
    --alexandria-database alexandria_dag_brain \
    --top-k 5 --brief
  ```

- **Offline JSONL query mode (without ArangoDB):**
  Replace `--arango --endpoint ... --database ...` with `--input-dir artifacts/alexandria_dag_brain` on either tool.

- **Formalization blueprint bridge (`blueprint_alexandria_bridge.py`):**
  Maps retrieved theorem/definition/proof chunks against local Lean declaration search records (`tools/infra/leansearch_local.py`) to draft candidate Lean formalization roadmaps before editing owner files:
  ```bash
  python3 tools/infra/blueprint_alexandria_bridge.py \
    --input-dir artifacts/alexandria_dag_brain \
    --out artifacts/alexandria_dag_brain/blueprint_nodes.jsonl
  ```

---

## 7. Verification

Run the offline Alexandria and environment isolation test suite without touching live ArangoDB services:
```bash
PYTHONDONTWRITEBYTECODE=1 /home/goutev/miniforge3/envs/sage/bin/python -m pytest -p no:cacheprovider -v \
  tests/alexandria tests/test_arango_env.py
```

Further architectural detail is in [HYBRID_GRAPHRAG.md](HYBRID_GRAPHRAG.md), copy-paste agent workflows are in [ALEXANDRIA_SKILL.md](ALEXANDRIA_SKILL.md), [skills/alexandria-pipeline/SKILL.md](../../skills/alexandria-pipeline/SKILL.md), and [the repository skill](../../.agents/skills/alexandria-pipeline/SKILL.md), and the full module/CLI/Docker reference lives in [tools/alexandria/README.md](../../tools/alexandria/README.md) and [configs/alexandria/README.md](../../configs/alexandria/README.md).
