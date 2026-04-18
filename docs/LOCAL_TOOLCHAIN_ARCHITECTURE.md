# Local Toolchain Architecture

This document describes the local execution architecture of the repository toolchain.
It is the operational topology for running Lean, DAG, Arango, LeanTrail, and hypothesis lanes on one machine (including DGX Spark setups).

Lean source and kernel checks remain the only authority surface.

## 1. Architectural Principles

- local-first execution: proof search, compilation, indexing, and policy gates run on local hardware
- authority separation: `.lean` + Lean kernel decide truth; external carriers are retrieval/analysis surfaces
- deterministic lanes: managed scripts enforce stable order, artifact paths, and policy checks
- typed handoff: research/proposal lanes must hand off through typed packets and compile gates
- failure visibility: freshness and policy health are explicitly surfaced (`dagStatus`, `dagDoctor`, strict-check)

## 2. Layered Topology

### 2.1 Authority Layer (Lean Kernel)

- compiler and elaborator: `lake`, `lake env lean`, module builds
- authority modules:
  - `lean/InfoGeometry/Audit.lean`
  - `lean/InfoGeometry/Meta/Architecture.lean`
- closure gates:
  - file gate: `lake env lean <file>.lean`
  - module gate: `python3 tools/infra/run_locked_lake_build.py <Module>`
  - repo gate: managed DAG lane + policy checks

### 2.2 Control Plane (Managed Lake Scripts)

User entrypoints live in `lakefile.lean` and call Python controllers:

- `lake script run changedVerify`
- `lake script run dagStatus`
- `lake script run dagRefresh`
- `lake script run dagReports`
- `lake script run dagDoctor`
- `lake script run dagAll`

This is the default operator surface.

### 2.3 DAG Structural Plane

Authoritative graph artifacts are generated from Lean environment data:

- `artifacts/dag/full_graph.json`
- `artifacts/dag/index/decls.jsonl`
- `artifacts/dag/index/edges.jsonl`
- `artifacts/dag/structural-topology.json`

Managed report orchestration is configured by:

- `dag-toolchain.json`

`dagReports` executes the configured report sequence in order and writes timing sidecars.

### 2.4 Expression Graph / Arango Plane

Expression-level graph export (De Bruijn + `bound_by`) is produced by:

- `lean/DAG/ExprArangoExport.lean`

Output shape:

- `ig_nodes.jsonl` (decl + expr nodes)
- `ig_edges.jsonl` (`ast`, `bind`, `const_ref`, `decl_root`)
- `metadata.json`

Optional ingestion:

- `python3 tools/leantrail/arango_ingest.py ...`

This plane is designed for structural retrieval and dedup analysis; it does not replace Lean authority.

### 2.5 Alpha-Dedup Plane

Alpha-equivalence style structural compression over expression graphs:

- `python3 tools/infra/generate_expr_alpha_dedup.py ...`

Outputs:

- `reports/dag/expr-alpha-dedup.json`
- `reports/dag/expr-alpha-dedup.md`

The script supports `--allow-missing-input` so managed lanes remain stable when expr-graph inputs are absent.

### 2.6 LeanTrail Parity Plane

LeanTrail snapshots are exported to multiple carriers and checked for parity:

- canonical snapshot: `artifacts/leantrail/graph_snapshot.json`
- adapters: GraphML / Neo4j CSV / Arango JSON
- conformance gate: `lake script run leantrailConformance ... --fail-on-violation`

Policy:

- canonical snapshot is truth carrier
- external DB formats are retrieval carriers

### 2.7 Hypothesis and Local Training Plane

Local link/hypothesis stack:

- dataset and scorer:
  - `build_link_ats_dataset.py`
  - `train_link_scorer.py`
  - `score_link_candidates.py`
  - `rerank_arango_links.py`
- dual-model hypothesis lane:
  - `dual_hypothesis_sampler.py`
  - `hypothesis_fuser_and_lean_gate.py`
- DGX orchestrator:
  - `dgx_spark_hybrid_orchestrator.py`

Closure remains Lean compile + strict checks.

### 2.8 Documentation Hygiene Plane

Markdown corpus classification/hygiene is treated as a local governance lane:

- classifier:
  - `python3 tools/infra/reports/classify_markdown_corpus.py ...`
- hygiene scorer:
  - `python3 tools/infra/reports/generate_markdown_hygiene_report.py ...`
- output surfaces:
  - `reports/dag/markdown-classification.{json,md}`
  - `reports/dag/markdown-hygiene.{json,md}`

Black Books corridors (`docs/black_books/**`) are excluded from automated
cleanup decisions; they remain protected exploration material.

## 3. Execution Graph (Operational View)

```text
Lean source (.lean)
  -> lake / lean elaboration
  -> DAG index export (artifacts/dag/*)
  -> managed reports (reports/dag/*)
  -> doctor/policy gates

Optional branch A:
  ExprArangoExport -> artifacts/expr-graph/arango/* -> Arango ingest -> graph queries / dedup reports

Optional branch B:
  LeanTrail snapshot -> external carriers -> conformance parity

Optional branch C:
  ATS dataset + scorer + hypothesis sampler/fuser -> Lean gate -> accepted local artifacts
```

## 4. Canonical Workflows

### 4.1 Patch Loop (default)

1. `lake env lean <changed-file>.lean`
2. `lake script run changedVerify`
3. `lake script run dagAll` at checkpoint/promotion time

### 4.2 Full Structural Refresh

1. `lake script run dagRefresh`
2. `lake script run dagReports`
3. `lake script run dagDoctor`

### 4.3 Expr-Graph + Dedup Loop

1. `lake env lean --run lean/DAG/ExprArangoExport.lean ...`
2. `python3 tools/infra/generate_expr_alpha_dedup.py ...`
3. optional: `python3 tools/leantrail/arango_ingest.py ...`

## 5. Config and Contracts

- DAG config: `dag-toolchain.json`
- report timing: `artifacts/dag/report-timing.json`
- index timing: `artifacts/dag/index/indexer-timing.json`
- lane policy and health:
  - `tools/infra/dag_status.py`
  - `tools/infra/dag_doctor.py`
- research/handoff contracts:
  - `docs/ResearchPacketContract.md`
  - `docs/CandidateBridgePacketContract.md`

## 6. Trust Order

If surfaces disagree, trust in this order:

1. Lean source + Lean compiler
2. authoritative DAG artifacts (`artifacts/dag/*`)
3. managed report layer (`reports/dag/*`)
4. external carriers (Arango/GraphML/Neo4j) after conformance validation

## 7. Extension Rule

When adding a new local analysis stage:

1. make outputs deterministic and path-stable
2. add stage in `dag-toolchain.json` report sequence (or explicit lane)
3. add `--allow-missing-input` if optional inputs are involved
4. document the stage in `tools/infra/README.md`
5. keep Lean closure gates unchanged
