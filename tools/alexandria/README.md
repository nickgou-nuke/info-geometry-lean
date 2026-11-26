<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](../../docs/REPO_DEEP_SEARCH_PROTOCOL.md).

# Alexandria Literature & PDF-to-DAG-Brain Pipeline (`tools/alexandria/`)

> Status: `maintained local guide`
> Source reviewed: 2026-11-24 at commit `9bbab55c38` (pipeline commits `ecd539dc9c`, `e423f7b867`).
> See: [README.md](../../README.md), [AGENTS.md](../../AGENTS.md), [docs/CANONICAL_AGENT_PIPELINE.md](../../docs/CANONICAL_AGENT_PIPELINE.md), [docs/alexandria/README.md](../../docs/alexandria/README.md), [configs/alexandria/README.md](../../configs/alexandria/README.md), [skills/alexandria-pipeline/SKILL.md](../../skills/alexandria-pipeline/SKILL.md)

`tools/alexandria/` owns the isolated literature, arXiv, AutoMathText-V2, and **PDF-to-DAG-brain** GraphRAG subsystem.

## 1. Authority Boundary

- Every document, section, chunk, entity, edge, and retrieval hit produced by Alexandria carries `sourceAuthority: "retrieval_context_only"` and the disclaimer `"Retrieval and navigation context only; NOT verified Lean proof evidence."`
- Alexandria locates mathematical papers, theorems, definitions, proofs, equations, citations, and cross-document conceptual neighborhoods. It **never** establishes Lean proof truth. Always descend to owner files under `lean/InfoGeometry/` and run `run_locked_lean.py` / `run_locked_lake_build.py`.

## 2. End-to-End PDF-to-DAG-Brain Architecture

```text
Read-only PDF corpus (`.pdf` + magic `%PDF-`)
  │
  ▼  tools/alexandria/pdf_corpus_ingest.py
     ├─ SHA-256 deduplication + deterministic canonical path selection
     ├─ --exclude-default-noise / --exclude-glob / --resume (.doc_cache)
     ├─ pdfinfo + pdftotext -enc UTF-8 (+ isolated pypdf fallback)
     ├─ 8 chunk archetypes + 10 mathematical domain archetypes
     ├─ cross-doc canonicalKey concepts + bibliography arXiv/DOI/title matching
     ├─ 6 acyclic DAG edge types verified by Kahn topological sort
     └─ optional bounded --enrich-ollama (Ollama /api/chat or OpenAI /v1)
  │
  ▼  10 JSONL artifacts + corpus_inventory_report.{json,md}
  │
  ▼  tools/alexandria/arango_ingest.py  (or --ingest-arango)
     ├─ dedicated isolated ArangoDB instance (:8532 default, or e.g. :8538)
     ├─ 4 document collections + 6 edge collections + persistent indexes
     └─ ArangoSearch BM25 view `alexandria_chunks_search` (text_en + searchTerms)
  │
  ├─► tools/alexandria/retrieve_context.py
  │     BM25 + exact searchTerms + 1-hop adjacent + 1..3-hop DAG BFS
  │     (--arango live OR --input-dir JSONL; pure stdlib)
  │
  ├─► tools/alexandria/graph_context_rank.py
  │     BM25/lexical seeds -> 200-chunk subgraph -> Personalized PageRank
  │     over adjacent + dag/dag_reverse + entity_relation + shared canonicalKey
  │     (requires `networkx`)
  │
  └─► tools/infra/ask_repo.py / tools/infra/graph_rag_query.py
        opt-in `--scope alexandria` (excluded from `--scope all`)
```

## 3. Container & Lane Isolation

Alexandria enforces strict runtime separation from the Lean declaration/InfoTree DAG and Hive queue lanes via [`src/igf/config/env_aliases.py`](../../src/igf/config/env_aliases.py) (re-exported by [`tools/infra/arango_env.py`](../infra/arango_env.py)):

| Lane | Source Default Endpoint / DB | Compose / Config | Allowed for Alexandria? |
|---|---|---|---|
| Lean Declaration / InfoTree DAG | `http://127.0.0.1:8530` / `infogeometry` (`darwin_commits` shares host) | `ARANGO_*`, `DARWIN_ARANGO_*` | **FORBIDDEN** (rejected) |
| Hive Queue & aiClaw RAG | `http://127.0.0.1:8540` / `hive_live` (`aiclaw_auto_rag`) | `HIVE_ARANGO_*`, `AICLAW_ARANGO_*` | **FORBIDDEN** (rejected) |
| **Default Alexandria PDF Lane** | `http://127.0.0.1:8532` / `alexandria` | [`configs/alexandria/docker-compose.pdf.yml`](../../configs/alexandria/docker-compose.pdf.yml) | Yes (default) |
| **Dedicated Isolated Brain** (e.g., observed `alexandria_dag_brain`) | `http://127.0.0.1:8538` / `alexandria_dag_brain` (via overrides) | `docker-compose.pdf.yml` + `ALEXANDRIA_ARANGO_*` | Yes (recommended for separate corpora) |

- `guard_alexandria_target(endpoint, database)` rejects `FORBIDDEN_ALEXANDRIA_PORTS = {8530, 8540}` and `FORBIDDEN_ALEXANDRIA_DATABASES = {"infogeometry", "darwin_commits", "hive_live", "aiclaw_auto_rag"}` (CLIs exit with status `2`).
- `load_alexandria_arango_env()` reads [`configs/alexandria/.env`](../../configs/alexandria/.env.example) (or `ALEXANDRIA_ARANGO_ENV_FILE`) **only without overriding** already-exported `ALEXANDRIA_*` variables, derives `http://127.0.0.1:${ALEXANDRIA_ARANGO_PORT}` when `ALEXANDRIA_ARANGO_ENDPOINT` is unset, and leaves `ARANGO_*` / `HIVE_*` untouched.
- Supported Alexandria env aliases: `ALEXANDRIA_ARANGO_ENDPOINT`, `ALEXANDRIA_ARANGO_PORT`, `ALEXANDRIA_ARANGO_DB` / `ALEXANDRIA_ARANGO_DATABASE`, `ALEXANDRIA_ARANGO_USERNAME` / `ALEXANDRIA_ARANGO_USER`, `ALEXANDRIA_ARANGO_PASSWORD` / `ALEXANDRIA_ARANGO_PASS`, `ALEXANDRIA_ARANGO_ENV_FILE`.

### Launching Isolated Alexandria Containers

Default `:8532` (`arango_alexandria_pdf`, DB `alexandria`):

```bash
docker compose -f configs/alexandria/docker-compose.pdf.yml up -d
```

Dedicated isolated container on a separate port and volumes (for example `:8538` / `alexandria_dag_brain`; never echo secrets in logs):

```bash
ALEXANDRIA_ARANGO_CONTAINER=arango_alexandria_dag \
ALEXANDRIA_ARANGO_PORT=8538 \
ALEXANDRIA_ARANGO_DATA_VOLUME=alexandria_dag_brain_data \
ALEXANDRIA_ARANGO_APPS_VOLUME=alexandria_dag_brain_apps \
docker compose -p alexandria_dag_brain -f configs/alexandria/docker-compose.pdf.yml up -d
```

> **Legacy compose warning:** [`configs/alexandria/docker-compose.yml`](../../configs/alexandria/docker-compose.yml) sets `container_name: arango_alexandria` (on this workstation that legacy container is bound to `:8530`, the Lean DAG lane). Prefer [`configs/alexandria/docker-compose.pdf.yml`](../../configs/alexandria/docker-compose.pdf.yml) for all Alexandria PDF/DAG-brain deployments.

## 4. PDF Ingestion, Archetypes, Acyclic DAG & Optional LLM Enrichment

[`pdf_corpus_ingest.py`](pdf_corpus_ingest.py) implements deterministic, read-only PDF processing:

1. **Walk & Deduplication**: Traverses `--input-dir` with `followlinks=False` (symlinks skipped), accepts `.pdf` extensions and non-`.pdf` files whose header contains `%PDF-`, streams SHA-256, and picks one deterministic canonical copy per digest (`_canonical_sort_key`). `--exclude-default-noise` excludes `*Isabelle2025*`, `*Act_Content*`, `*OV2640_DS*`, and `*JFETS_The_New_Frontier*`; additional `--exclude-glob` flags are repeatable.
2. **Resilient Extraction**: Runs `pdfinfo` + `pdftotext -enc UTF-8`, falling back to an isolated subprocess `pypdf` worker if `pdftotext` fails or returns empty text. Normalizes ligatures/control characters, strips standalone page numbers and repeated running headers/footers, detects encoding noise (`\ufffd`, private-use glyphs, Type3 remaps) and cover-only scanned PDFs, and classifies each SHA-256 group into `OUTCOME_KEYS`: `ingested`, `duplicate_skipped`, `empty_0_bytes`, `scanned_no_text`, `encrypted_no_text`, `very_low_text_skipped`, `parse_error`, `limit_skipped`. `--resume` enables per-SHA atomic caching under `<output_dir>/.doc_cache/<sha256>_<max_chunk_chars>.json` keyed by `SCHEMA_VERSION` (`info_geometry.alexandria.semantic_ingest.v2`).
3. **Chunk Archetypes (`chunkKind`)**: Segments sections (including two-line numbered headings) and classifies blocks into 8 archetypes: `abstract`, `theorem`, `definition`, `proof`, `remark`, `equation` (guarded by `_is_displayed_equation_block` against prose equation-number false positives), `bibliography`, `prose`.
4. **Domain Archetypes & Cross-Doc Linking**: Tags chunks with 10 `MATH_ARCHETYPE_PATTERNS`:
   - `z2_graded_polarization`, `curved_dga_differential`, `clifford_spinor_tower`, `krein_indefinite_metric`, `drazin_riesz_spectral`, `souriau_metriplectic_thermo`, `modular_kms_monodromy`, `categorical_colimit_tower`, `noncommutative_k_theory`, `yang_mills_gauge_holonomy`.
   - Emits deterministic cross-document `canonicalKey` (`stable_key("concept", entity_type, norm)`) on shared concepts (`math_symbol`, `defined_term`, `math_archetype`, `llm_entity`) while keeping `math_label`, `math_reference`, and `bib_entry` document-local (`canonicalKey: ""`).
5. **Strictly Acyclic DAG (`alexandria_dag_edges`)**: Emits 6 typed DAG relations in priority order (`DAG_EDGE_PRIORITY`):
   1. `section_precedes_section`
   2. `proof_proves_theorem`
   3. `chunk_cites_entry`
   4. `chunk_uses_definition`
   5. `chunk_references_result`
   6. `document_cites_document` (resolved across the corpus via arXiv ID preferring highest version, DOI, or normalized title anchor)
   Then runs `verify_and_prune_dag()` to drop cycle-closing edges and verify topological acyclicity with Kahn's algorithm.
6. **Optional Bounded LLM Enrichment (`--enrich-ollama`)**: Supports both native Ollama (`/api/tags`, `/api/chat`) and OpenAI-compatible `/v1` endpoints (`/v1/models`, `/v1/chat/completions`), including Qwen3 hardening:
   - Priority-ranks chunks (`theorem`, `definition`, `abstract`, `remark`, `proof`, `equation`, `prose`) up to `--enrich-ollama-max-chunks`.
   - Disables thinking by default on `/v1` (`chat_template_kwargs: {"enable_thinking": false}`; pass `--allow-thinking` to re-enable), strips `<think>...</think>` blocks and markdown fences, extracts balanced JSON objects, bounds concurrency via `--enrich-ollama-workers` and `--enrich-ollama-max-tokens`, supports bearer auth via `--enrich-ollama-api-key` or `ALEXANDRIA_LLM_API_KEY` / `OPENAI_API_KEY`, trips a circuit breaker after `--enrich-ollama-max-failures` consecutive failures, and materializes `llm_entity` nodes, `alexandria_chunk_entity_edges`, `alexandria_entity_relation_edges`, and `searchTerms`.

## 5. ArangoDB Schema & BM25 View (`arango_ingest.py`)

[`arango_ingest.py`](arango_ingest.py) uses [`igf.graph.arango_http`](../../src/igf/graph/arango_http.py) (no `python-arango` dependency) to populate:

- **Document collections**: `alexandria_documents`, `alexandria_sections`, `alexandria_chunks`, `alexandria_entities`
- **Edge collections**: `alexandria_document_section_edges`, `alexandria_section_chunk_edges`, `alexandria_chunk_adjacent_edges`, `alexandria_chunk_entity_edges`, `alexandria_entity_relation_edges`, `alexandria_dag_edges`
- **Persistent indexes**: includes `path`/`title`/`contentHash` on documents; `documentKey`/`title` on sections; `documentKey`/`sectionKey`/`chunkKind`/`tokens[*]` on chunks; `chunkKey`/`entityType`/`surface`/`documentKey`/`normalized`/`canonicalKey` on entities; `chunkKey` on entity relations; `documentKey`/`edgeType` on DAG edges.
- **ArangoSearch view (`alexandria_chunks_search`)**: BM25 over `text` (`text_en`), `title` (`text_en`, `identity`), and `identity` on `searchTerms`, `chunkKind`, `documentKey`, and `provenance.{path,declName,sourceFormat,sourceKind}`. `add_search_terms()` indexes identifier pieces plus `semantic.{mathematical_archetypes, mathematical_entities, assumed_definitions, symbolic_terms}`.

## 6. Operator Commands

### 6.1 Ingest a PDF Corpus to JSONL and ArangoDB

```bash
python3 tools/alexandria/pdf_corpus_ingest.py \
  --input-dir /path/to/pdfs \
  --output-dir artifacts/alexandria_dag_brain \
  --exclude-default-noise \
  --resume \
  --workers 4 \
  --ingest-arango \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --replace-documents
```

Useful standalone ArangoDB ingest / refresh flags (`arango_ingest.py`):

```bash
python3 tools/alexandria/arango_ingest.py \
  --input-dir artifacts/alexandria_dag_brain \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --skip-unchanged   # or --replace-documents, or --search-view-only
```

### 6.2 BM25 + Multi-Hop DAG Retrieval (`retrieve_context.py`)

Pure stdlib + repo modules; works with default `python3`:

```bash
# Live ArangoDB BM25 + searchTerms + 1-hop adjacent + 1..3-hop DAG BFS
python3 tools/alexandria/retrieve_context.py \
  --arango \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --query "Krein space fundamental symmetry Peirce decomposition" \
  --top-k 5 --hops 2 --format text

# Offline JSONL mode (no running ArangoDB needed)
python3 tools/alexandria/retrieve_context.py \
  --input-dir artifacts/alexandria_dag_brain \
  --query "Krein space fundamental symmetry Peirce decomposition" \
  --top-k 5 --hops 2 --format json
```

### 6.3 Personalized PageRank Subgraph Ranking (`graph_context_rank.py`)

Requires **`networkx`**. On this workstation, bare `python3` in `PATH` may resolve to `OpenGauss/venv/bin/python3` (which lacks `networkx`); use `.venv/bin/python3`, `.venv-py312/bin/python3`, or `/home/goutev/miniforge3/envs/sage/bin/python`:

```bash
.venv/bin/python3 tools/alexandria/graph_context_rank.py \
  --arango \
  --endpoint http://127.0.0.1:8538 \
  --database alexandria_dag_brain \
  --query "Drazin inverse Riesz projector spectral decomposition" \
  --top-k 5 --seed-k 5 --hops 2 --format text
```

Offline JSONL ranking is also supported via `--input-dir <dir>` (note `--hops` applies to `--arango` AQL DAG expansion; `--use-gpu` enables optional cuGraph backend hints with NetworkX fallback).

### 6.4 Unified Repo GraphRAG Explorer (`ask_repo.py` / `graph_rag_query.py`)

Alexandria is **opt-in** via `--scope alexandria` (it is intentionally **not** queried by `--scope all`):

```bash
python3 tools/infra/ask_repo.py \
  "Krein space fundamental symmetry Peirce decomposition" \
  --scope alexandria \
  --alexandria-endpoint http://127.0.0.1:8538 \
  --alexandria-database alexandria_dag_brain \
  --top-k 5 --brief

# Combine Lean declarations + docs + Alexandria PDFs in one explorer packet:
python3 tools/infra/graph_rag_query.py \
  "Drazin inverse Riesz projector" \
  --scope lean,docs,alexandria \
  --alexandria-endpoint http://127.0.0.1:8538 \
  --alexandria-database alexandria_dag_brain \
  --top-k 5 --format md
```

## 7. Complete Script Inventory (`tools/alexandria/`)

| Category | Module | Role |
|---|---|---|
| **PDF-to-DAG-Brain Core** | [`pdf_corpus_ingest.py`](pdf_corpus_ingest.py) | PDF corpus walk, SHA-256 dedup, extraction, archetypes, cross-doc citation & concept linking, Kahn-verified acyclic DAG, optional Ollama/`/v1` enrichment, optional Arango ingest |
| | [`arango_ingest.py`](arango_ingest.py) | Stdlib HTTP ArangoDB schema/index/JSONL importer + `alexandria_chunks_search` BM25 view manager |
| | [`retrieve_context.py`](retrieve_context.py) | Dual-mode (`--arango` / `--input-dir`) BM25 + `searchTerms` + adjacent + `alexandria_dag_edges` BFS retriever |
| | [`graph_context_rank.py`](graph_context_rank.py) | Dual-mode NetworkX Personalized PageRank over adjacent, `dag`/`dag_reverse`, entity-relation, and `canonicalKey` cross-doc edges |
| | [`schema.py`](schema.py) | `SCHEMA_VERSION`, `DAG_EDGE_COLLECTION`, `DAG_EDGE_TYPES`, collection lists, `stable_key`, `content_hash`, endpoint validators |
| **Text, LaTeX & arXiv Ingest** | [`semantic_ingest.py`](semantic_ingest.py) | Markdown/text/Lean/LaTeX semantic chunk, entity, and relation JSONL builder |
| | [`structural_chunking.py`](structural_chunking.py) | Shared identifier/text tokenization (`tokenize`, `ident_terms`) and structural text chunking |
| | [`math_paper_graphrag_ingest.py`](math_paper_graphrag_ingest.py) | LaTeX-aware math paper chunking for Alexandria/GraphRAG |
| | [`fetch_arxiv_corpus.py`](fetch_arxiv_corpus.py) | Downloads a small arXiv corpus into source-aware markdown cache files |
| **AutoMathText-V2 & txt2kg** | [`download_automathtext_v2.py`](download_automathtext_v2.py) | Plans or downloads AutoMathText-V2 shards safely |
| | [`automathtext_v2_ingest.py`](automathtext_v2_ingest.py) | Converts AutoMathText-V2 shards into `automath_*` theorem-context JSONL |
| | [`automathtext_arango_ingest.py`](automathtext_arango_ingest.py) | Ingests `automath_*` theorem-context JSONL into ArangoDB |
| | [`verify_automathtext_arango_descent.py`](verify_automathtext_arango_descent.py) | Non-mutating verifier for AutoMathText-V2 epistemic ancestry descent |
| | [`txt2kg_hive_ingest.py`](txt2kg_hive_ingest.py) | Digests text libraries into retrieval-only `txt2kg_*` triples and optional Hive tasks |
| **Analysis, Dossier & Repair** | [`alexandria_algorithms.py`](alexandria_algorithms.py) | Local JSONL graph overlays, anchor/weak entity diagnostics, and defect metrics |
| | [`artifact_ast_lint.py`](artifact_ast_lint.py) | AST-aware artifact digest and lint pipeline for papers/textbooks |
| | [`recover_pdf_source_fragments.py`](recover_pdf_source_fragments.py) | Recovers text-layer source fragments and code blocks from math PDFs |
| | [`batch_check_recovered_lean.py`](batch_check_recovered_lean.py) | Batch-checks `recovered_pdf_code_blocks.jsonl` snippets with `lake env lean` |
| | [`conductive_context_to_lean_skeleton.py`](conductive_context_to_lean_skeleton.py) | Converts conductive Alexandria context into reviewable Lean skeleton artifacts |
| | [`materialize_coarse_scc_overlay.py`](materialize_coarse_scc_overlay.py) | Materializes SCC coarse-graining overlay JSONL from Alexandria artifacts |
| | [`proof_synthesis_report.py`](proof_synthesis_report.py) | Builds witness-backed proof synthesis prompts from Alexandria SCC discovery |
| | [`render_socratic_dossier.py`](render_socratic_dossier.py) | Renders a Socratic dossier from an Alexandria context packet |
| | [`repair_lineage.py`](repair_lineage.py) | Records Alexandria repair lineage for a broken node and compiler-gated candidate |

## 8. Testing & Guardrails

Unit test suite (pure offline / mocked Arango HTTP):

```bash
/home/goutev/miniforge3/envs/sage/bin/python -m pytest \
  tests/alexandria/test_pdf_corpus_ingest.py \
  tests/alexandria/test_retrieve_context.py \
  tests/alexandria/test_graph_context_rank.py \
  tests/alexandria/test_arango_ingest.py \
  tests/alexandria/test_graph_rag_alexandria_scope.py \
  tests/test_arango_env.py -q
```

5-tier E2E suite ([`tests/e2e_alexandria_pdf/`](../../tests/e2e_alexandria_pdf/)): exercises live PDF generation, ingestion, ArangoDB `:8532` persistence into isolated ephemeral test DBs (strictly refusing protected ports `8530`/`8540` and protected databases `alexandria`, `infogeometry`, `darwin_commits`, `hive_live`, `aiclaw_auto_rag`), cross-feature pipelines, read-only real-corpus checks, and adversarial edge cases.

## 9. Observed Workstation Verification Snapshot (2026-11-23 / 2026-11-24)

The figures below record an observed workstation deployment (`arango_alexandria_dag` on `http://127.0.0.1:8538`, database `alexandria_dag_brain`) and are **not** guaranteed present on fresh clones:

- **Ingested corpus (`artifacts/alexandria_dag_brain/corpus_inventory_report.json`)**:
  - `53,303` regular files scanned (`914` symlinks skipped; `48,567` non-PDF skipped with `--exclude-default-noise`)
  - `4,736` PDFs discovered (`4,727` `.pdf` + `9` magic `%PDF-` non-`.pdf`) -> `3,446` unique SHA-256 (`1,290` duplicates skipped)
  - `3,373` ingested (`69` scanned/no-text, `2` encrypted, `2` very-low-text, `0` parse errors)
  - `71,976` sections, `265,512` chunks (`theorem`: `39,918`; `proof`: `26,096`; `definition`: `10,532`; `equation`: `12,951`; `remark`: `14,702`; `abstract`: `1,538`; `bibliography`: `9,409`; `prose`: `150,366`), `999,535` entities, `187,341` entity-relation edges, and `269,420` acyclic DAG edges (`59` cycle-closing edges pruned; `3,194` `document_cites_document` links).
- **Live query checks verified on 2026-11-24 against `:8538` / `alexandria_dag_brain`**:
  - `retrieve_context.py --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain --query "Krein space fundamental symmetry Peirce decomposition" --top-k 5 --hops 2`: returned 5 hits (BM25 scores `59.783`–`65.762`) across `2103.04372v1.pdf`, `mccrimmon_jordan.pdf`, and `0110001v2.pdf`, with `dagNeighbors` links (`chunk_uses_definition`, `chunk_cites_entry`).
  - `graph_context_rank.py --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain --query "Drazin inverse Riesz projector spectral decomposition" --top-k 5 --hops 2` (run under `/home/goutev/miniforge3/envs/sage/bin/python`): built a `35`-node, `702`-edge cross-document subgraph and returned 5 ranked hits across `2208.09149v1.pdf` (`0.0634`), `L-G-0010374276-0023403328.pdf` (`0.0632`, `0.0601`, `0.0594`), and `on_drazin.pdf` (`0.0614`).
