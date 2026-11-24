# DAG Toolchain and Alexandria Trace

> Status: `maintained operations trace`
> Audited: 2026-05-14 against the current scripts (Alexandria PDF-to-DAG-brain retrieval and lane-isolation trace refreshed 2026-11-24 against commit `9bbab55c38`).
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md), [tools/alexandria/README.md](../tools/alexandria/README.md)

This document records the analysis chain and toolchain usage map for the managed DAG lane, `tools/infra`, and `tools/alexandria`.

It is written as an explicit reasoning trace for operators: what was inspected, why it was inspected, and what coupling points were identified.

## Scope and Inputs

Primary scope:
- `dag-toolchain.json`
- `tools/infra/dag_*.py`
- `tools/infra/refresh_decl_graph.py`
- `tools/infra/run_full_dag_toolchain.py`
- `tools/infra/arango_*.py`
- `tools/infra/*raw_infotree*`
- `tools/alexandria/*.py`
- Lean-side references under `lean/DAG/` and `lean/InfoGeometry/Meta/`
- Lake script bindings in `lakefile.lean`

Inventory snapshot:
- `tools/infra/`: 156 python files (historical 2026-05-14 snapshot)
- `tools/alexandria/`: 23 non-`__init__` python scripts/modules plus `__init__.py` and `README.md` (refreshed 2026-11-24)

## Analysis Chain (Reasoning Trace)

### 1) Establish DAG operator lane entrypoints

Inspected:
- `dag-toolchain.json`
- `tools/infra/dag_config.py`
- `tools/infra/dag_refresh.py`
- `tools/infra/dag_reports.py`
- `tools/infra/dag_status.py`
- `tools/infra/dag_doctor.py`
- `tools/infra/dag_manifest.py`
- `tools/infra/dag_all.py`

Reason:
- Verify the managed lane contract, execution order, and what artifacts are treated as authoritative vs derived.

Findings:
- `dag-toolchain.json` is the lane contract: build target/import root/namespace/run mode + derived report sequence + policy thresholds.
- `dag_refresh.py` calls `refresh_decl_graph.py` using config-resolved paths.
- `dag_reports.py` runs configured report sequence and writes report timing sidecar.
- `dag_status.py` and `dag_doctor.py` are observability/diagnostic surfaces.
- `dag_manifest.py` stamps a single manifest over refreshed state.
- `dag_all.py` composes status -> refresh -> reports -> doctor.
- `run_full_dag_toolchain.py` is a separate strict local pipeline. It does not
  read `dag-toolchain.json`, and it is not the same execution contract as
  `dagAll`.

### 2) Verify build locking and reproducibility controls

Inspected:
- `tools/infra/build.py`
- `tools/infra/run_locked_lake_build.py`
- `tools/build_lock.py`

Reason:
- Check whether refresh/report paths are protected from concurrent lake-build contamination.

Findings:
- Shared lock path: `/tmp/info-geometry-build.lock`.
- `run_locked_lake_build` is the build gate used by refresh prebuild.
- `refresh_decl_graph.py` uses locked prebuild and content hashes (`olean` + source hash) for incremental skip behavior.

### 3) Trace Lake script wiring (operator UX)

Inspected:
- `lakefile.lean`

Reason:
- Confirm operator-facing script names and their backing Python entrypoints.

Findings:
- Explicit scripts: `dagStatus`, `dagRefresh`, `dagReports`, `dagDoctor`, `dagAll`.
- Scripts are thin wrappers to `tools/infra/dag_*.py`, preserving stable operator commands.

### 4) Separate Lean metaprogramming layer from Python orchestration layer

Inspected:
- `lean/InfoGeometry/Meta/Architecture.lean`
- `lean/InfoGeometry/Meta/Vacuity.lean`
- `lean/DAG/Indexer.lean`

Reason:
- Identify where semantic authority and tag grammar are defined.

Findings:
- Lean owns metaprogramming semantics (`rep_depth`, `capstone`, vacuity tags, audit commands).
- `Indexer.lean` imports these tag surfaces and exports attrs onto declaration rows.
- Python does not implement Lean metaprogramming; it orchestrates and validates artifacts produced from Lean-owned semantics.

### 5) Trace Arango usage by domain (core DAG vs Alexandria)

Inspected:
- Core DAG/InfoTree ingest and analytics:
  - `tools/leantrail/arango_ingest.py`
  - `tools/infra/arango_layered_ingest.py`
  - `tools/infra/arango_raw_infotree_ingest.py`
  - `tools/infra/arango_dag_algorithms.py`
  - `tools/infra/hydrate_arango_topology.py`
- Alexandria ingest and retrieval:
  - `tools/alexandria/pdf_corpus_ingest.py`
  - `tools/alexandria/arango_ingest.py`
  - `tools/alexandria/retrieve_context.py`
  - `tools/alexandria/semantic_ingest.py`
  - `tools/alexandria/graph_context_rank.py`
  - `tools/alexandria/alexandria_algorithms.py`

Reason:
- Prevent conflating distinct graph domains sharing Arango transport.

Findings:
- Core lane uses Arango for theorem/dependency/overlay graph analytics and raw infotree projections (`:8530` / `infogeometry`).
- Alexandria lane uses isolated Arango instances (`:8532` default `alexandria` or dedicated isolated brains like `:8538` `alexandria_dag_brain`) for document/section/chunk/entity/DAG retrieval graph persistence (`retrieval_context_only`).
- `guard_alexandria_target()` prevents Alexandria tools from writing to `:8530` or `:8540`.

### 6) Trace elan/lake references

Inspected:
- `tools/infra/lean_interact_wrapper.py`
- `tools/infra/batch_raw_infotree_export.py`
- DAG wrappers and build tooling files above

Reason:
- Determine whether execution depends on explicit elan paths or generic `lake` resolution.

Findings:
- Most DAG lane calls rely on `lake` on PATH.
- Explicit elan references appear in targeted wrappers:
  - PATH prepend of `~/.elan/bin` (`lean_interact_wrapper.py`)
  - default lake executable `/home/goutev/.elan/bin/lake` (`batch_raw_infotree_export.py`)

## Toolchain Usage Map

## Managed DAG lane

Operator commands:
- `lake script run dagStatus`
- `lake script run dagRefresh`
- `lake script run dagReports`
- `lake script run dagDoctor`
- `lake script run dagAll`

Lifecycle:
1. Status/diagnose current artifact freshness.
2. Refresh authoritative DAG artifacts from Lean indexer.
3. Run derived report sequence from config.
4. Diagnose policy/freshness/environment and suggest next commands.

The current `dagAll` wrapper performs exactly:

```text
dagStatus -> dagRefresh -> dagReports -> dagDoctor
```

It stops at the first failing stage. If `dagRefresh` fails because
`InfoGeometry.All` does not build, the later reports are not fresh.

## Authoritative export chain

1. Lean indexer (`lean/DAG/Indexer.lean`) emits DAG artifacts.
2. `tools/infra/refresh_decl_graph.py` orchestrates prebuild + indexer run + metadata stamp.
3. Authoritative outputs under `artifacts/dag/`:
   - `full_graph.json`
   - `index/{decls,edges,morphisms,types}.jsonl`
   - `structural-topology.json`

## Derived report chain

- `tools/infra/dag_reports.py` reads `dag-toolchain.json` `reportSequence` and executes each step.
- Outputs under `reports/dag/` and timing sidecars under artifacts lane.
- Current managed reports include `generate_expr_alpha_dedup.py` and
  `generate_source_sink_compression.py`.
- `generate_structural_dedup.py` and `generate_semantic_quotient.py` are
  explicit side tools, not current `dagReports` steps.

## Source closure-debt scanner

`tools/quality/closure_debt_crawler.py` is a source-level scanner despite its
historical filename. It scans Lean files and reports proof holes, global
assumptions, skeletal proofs, vacuous props, witness packaging, and placeholder
surfaces.

It is not a DAG reachability engine and is not an Arango pass. Use it to
identify open sockets and empty owners in source text, especially when
`dagRefresh` is blocked.

## Arango chains

### Core theorem/graph lane

- Lean export -> JSONL (`ig_nodes`, `ig_edges`, topology overlays, raw infotree rows)
- Ingest scripts populate Arango collections.
- Overlay analytics scripts compute additional navigation/diagnostic views.
- This lane is downstream of the native Lean DAG export. If `dagDoctor` reports
  stale source/olean hashes, live Arango cannot be treated as current.

### Alexandria retrieval lane

See [`tools/alexandria/README.md`](../tools/alexandria/README.md) and [`docs/alexandria/README.md`](alexandria/README.md) for full details:

- `pdf_corpus_ingest.py` walks PDF corpora read-only, deduplicates by SHA-256, extracts sections/chunks/10 mathematical archetypes/`canonicalKey` concepts, builds strictly acyclic `alexandria_dag_edges` verified via Kahn topological sort, and optionally enriches chunks via Ollama or OpenAI-compatible `/v1` endpoints.
- `semantic_ingest.py` and `math_paper_graphrag_ingest.py` build chunks/entities/relations JSONL from repo docs, Markdown, and LaTeX papers.
- `retrieve_context.py` retrieves BM25 + `searchTerms` + 1-hop adjacent + 1..3-hop `alexandria_dag_edges` BFS context (`--arango` or `--input-dir`).
- `graph_context_rank.py` computes Personalized PageRank over local or Arango-expanded subgraphs (adjacent, DAG, entity-relation, `canonicalKey`, and optional De Bruijn edges; requires `networkx`).
- `arango_ingest.py` (or `pdf_corpus_ingest.py --ingest-arango`) persists to isolated Alexandria ArangoDB collections and maintains `alexandria_chunks_search` (`:8530`/`:8540` blocked by `guard_alexandria_target`).

### Live GraphRAG verification (:8538 / `alexandria_dag_brain`)

Both retrieval CLIs accept a mutually exclusive local mode (`--input-dir`) and
live mode (`--arango`). Live retrieval requires the explicit `--arango` flag.
Endpoint/database/credentials come from `configs/alexandria/.env` or the
`ALEXANDRIA_ARANGO_*` environment aliases; defaults are `http://127.0.0.1:8532`
and database `alexandria`. `guard_alexandria_target` rejects the core DAG port
`:8530` and Hive port `:8540`, plus the `infogeometry`, `darwin_commits`,
`hive_live`, and `aiclaw_auto_rag` databases. The `:8538` target used below is
an allowed operational override; here the live database is
`alexandria_dag_brain`.

Use the repo venv (it has both `networkx` and `python-arango`):

```bash
.venv/bin/python3 tools/alexandria/retrieve_context.py \
  --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
  --query "Krein space fundamental symmetry Peirce decomposition" \
  --top-k 5 --hops 2 --format text
```

Observed: 5 BM25-ranked hits with scores from about `59.78` to `65.76`,
across `2103.04372v1.pdf`, `mccrimmon_jordan.pdf`, and `0110001v2.pdf`.
The packet records `scoreBreakdown.bm25`, lexical overlap, and a title flag,
plus entity and DAG-neighbor context.

```bash
.venv/bin/python3 tools/alexandria/graph_context_rank.py \
  --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
  --query "Drazin inverse Riesz projector spectral decomposition" \
  --top-k 5 --hops 2 --format text
```

Observed: a 35-node, 702-edge cross-document subgraph with 5 ranked hits;
top graph scores were `0.0634` (`2208.09149v1.pdf`), `0.0632`, `0.0601`,
`0.0594` (`L-G-0010374276-0023403328.pdf`), and `0.0614` (`on_drazin.pdf`).
The seeds come from BM25/lexical overlap and are reranked by personalized
PageRank over adjacency, shared-entity, DAG, and optional De Bruijn edges.

Both packets carry:
`authority = retrieval_context_only` and
`disclaimer = "Retrieval and navigation context only; NOT verified Lean proof evidence."`
Treat these results as source-discovery evidence only; Lean owner files and
kernel checks remain the truth authority.

## Coupling Points

High-coupling interfaces to keep stable:
- `dag-toolchain.json` schema and reportSequence contract.
- Artifact filenames/locations in `artifacts/dag/index/*`.
- `meta.json` fields (`schemaVersion`, `importRoot`, `nsFilter`, hashes).
- Arango collection names expected by ingest/verify/algorithm scripts.
- Lake script names in `lakefile.lean` used by operators and automation.

## Risk Notes

- Hardcoded defaults (notably explicit `~/.elan/bin/lake` style defaults) reduce portability.
- Shared lock hygiene is critical because build-lock state gates multiple pipelines.
- JSONL schema drift can silently break downstream tooling if not validated end-to-end.
- Keep Lean metaprogramming semantics as authority; Python should remain derivational/operational.

## Maintenance Guidance

- If `dag-toolchain.json` changes, update this trace and `tools/infra/dag_config.py` expectations together.
- If Arango collections are renamed, patch ingest + verify + algorithm consumers in one change.
- Prefer `lake script run dagAll` for operator closure when diagnosis indicates multiple stale surfaces.
- Treat this document as a living operations trace and refresh whenever managed lane contracts change.
