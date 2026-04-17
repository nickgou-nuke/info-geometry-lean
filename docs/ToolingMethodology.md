# Tooling Methodology

This document is the exact operational methodology for running the maintained
tooling surfaces in this repository.

It is an operator runbook, not a conceptual note.

## Rules

- use Lake-managed entrypoints by default
- use raw Python or Lean commands only when repairing or narrowing a tool failure
- run the DAG lane sequentially, not in parallel
- do not run the full DAG lane (`dagAll`) for every patch; use targeted module builds and `changedVerify` first
- do not trust `reports/dag/*` as current until the managed refresh and report sequence has finished
- do not hand-edit `artifacts/dag/*` or generated `reports/dag/*`

## Fast Entry Surface

Use the compressed wrappers first:

```bash
lake script run changedVerify
lake script run dagAll
lake script run dagDoctor
```

Use the longer managed or raw sequences only when the compressed lane is not enough.

## Choose The Lane

Use the tooling by question:

- source or theorem change
  - run Lean file gates and then the appropriate umbrella build
- whole-repo structure, coverage, ownership, hotspots, or report refresh
  - run the DAG lane under `tools/infra`
- semantic block structure, proof state, or declaration value printout
  - run the frontier lane under `tools/frontier`

## Method 0: LeanTrail Memory Carrier Parity

Use this when exporting LeanTrail to external memory carriers (GraphML, Neo4j,
Arango) and you need proof that exports preserve canonical structure.

1. Build/refresh canonical snapshot.

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json
```

2. Export adapters.

```bash
lake script run leantrailExport \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --to all
```

3. Run conformance gates against each carrier.

```bash
lake script run leantrailConformance \
  --baseline artifacts/leantrail/graph_snapshot.json --baseline-format snapshot \
  --candidate artifacts/leantrail/graph_snapshot.graphml --candidate-format graphml \
  --fail-on-violation

lake script run leantrailConformance \
  --baseline artifacts/leantrail/graph_snapshot.json --baseline-format snapshot \
  --candidate artifacts/leantrail/neo4j --candidate-format neo4j-csv \
  --fail-on-violation

lake script run leantrailConformance \
  --baseline artifacts/leantrail/graph_snapshot.json --baseline-format snapshot \
  --candidate artifacts/leantrail/arango --candidate-format arango-json \
  --fail-on-violation
```

Policy:
- `.olean` + canonical LeanTrail snapshot remain truth carriers.
- external DB/graph formats are retrieval carriers only.
- any nonzero conformance drift blocks ingestion.

## Method 1: Source Change Verification

Use this after editing Lean source.

1. Run the narrow file gate on each changed file.

```bash
lake env lean lean/InfoGeometry/Canonical/FisherVolumeBridge.lean
```

2. Run the correct umbrella build under the locked wrapper.

Canonical-only work:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

Whole-repo work:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

Architecture or representation-depth policy work:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
```

## Method 2: Managed DAG Refresh

Use this for the normal maintained whole-repo structural lane.

Shortest path:

```bash
lake script run dagAll
```

Expanded path:

1. Inspect current state.

```bash
lake script run dagStatus
```

2. Refresh the authoritative DAG artifacts.

```bash
lake script run dagRefresh
```

3. Regenerate the managed report layer.

```bash
lake script run dagReports
```

4. Confirm freshness and policy health.

```bash
lake script run dagDoctor
```

This is the normal exact sequence.

The current managed `dagReports` sequence regenerates:

- `reports/dag/repository-surface-index.{md,json}`
- `reports/dag/theorem-surface-index.{md,json}`
- `reports/dag/source-sink-compression.{md,json}`
- `reports/dag/true-root-order.{md,json}`
- `reports/theorem-significance.{md,json}`
- `reports/dag/sorry-equivalence.{md,json}`
- `reports/dag/declaration-networkx*.graphml`
- `reports/dag/module-networkx*.{graphml,svg,json}`
- `reports/dag/frontier-burndown.{md,json}`
- `reports/dag/replacement-frontier.{md,json}`

`reports/dag/repository-surface-index.{md,json}` is the canonical typed inventory
for tracked repository files. It scans `git ls-files` and classifies the full
tracked surface into Lean, Markdown, Python, and configuration classes.
For exhaustive local audits that also include untracked non-ignored files, run
`python3 tools/infra/reports/generate_repository_surface_index.py --include-untracked`.

## Method 3: Raw DAG Repair (Lean + Python)

Use this only when the managed lane fails and you need exact stage control.
Run sequentially.

### 3A. Full Strict Sequence

Use this when coverage must be strict and any partial graph should fail.

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/reports/generate_repository_surface_index.py --md-out reports/dag/repository-surface-index.md --json-out reports/dag/repository-surface-index.json
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_hypothesis_debt_report.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/theorem_significance.py --out reports/theorem-significance-current.json --md reports/theorem-significance-current.md
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py
python3 tools/infra/generate_replacement_frontier.py
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
python3 tools/infra/dag_status.py
python3 tools/infra/dag_doctor.py
```

Notes:
- `generate_causal_report.py` can fail on partial coverage by design.
- `canonical_policy_lint.py` is a debt gate and may fail even when artifacts are fresh.

### 3B. Partial-Coverage Diagnostic Variant

Use this when you intentionally want current diagnostics even if coverage is partial.

```bash
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json --allow-partial-coverage
python3 tools/infra/dag_status.py
python3 tools/infra/dag_doctor.py
```

### 3C. Process-Flow Lane

```bash
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

The Lean export is the authoritative process-flow surface.
The Python report step derives cocycles/comparison candidates and can be heavy on large snapshots.

### 3D. Full Theory-Graph Snapshot (Lean + DAG + Debt + Doctor)

Use this when you want one reproducible end-to-end state check before planning
major refactors or publishing an audit note.

```bash
lake build -R
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/reports/generate_repository_surface_index.py --md-out reports/dag/repository-surface-index.md --json-out reports/dag/repository-surface-index.json
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json --allow-partial-coverage --allow-uncovered-debt
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py || true
python3 tools/infra/generate_replacement_frontier.py
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
python3 tools/infra/dag_doctor.py
python3 tools/theorem_significance.py --out reports/theorem-significance-current.json --md reports/theorem-significance-current.md
python3 tools/infra/generate_hypothesis_debt_report.py --json-out reports/dag/hypothesis-debt-new-corpus.json --md-out reports/dag/hypothesis-debt-new-corpus.md
python3 tools/infra/reports/generate_vacuity_index.py --out reports/dag/hypothesis-vacuity-debt-current.md
python3 tools/infra/reports/generate_bridge_thinness_index.py
python3 tools/infra/reports/generate_surrogate_index.py
```

Notes:
- `canonical_policy_lint.py` is a regression gate and can fail on active debt.
- `dag_doctor.py` can fail on coverage policy while still reporting fresh artifacts.
- `generate_process_flow_report.py` can run significantly longer than the core DAG lane.

## Method 4: Frontier Semantic And Proof-State Work

Use this when the question is local elaboration, proof state, or declaration
value, not whole-repo structure.

### 4A. Cold One-Shot Proof Term

Use the cheapest maintained cold path when you already know the declaration.

```bash
lake script run proofPrint \
  lean/InfoGeometry/Canonical/FisherVolumeBridge.lean \
  --decl-name InfoGeometry.Canonical.FisherVolumeBridge.action_hessian_eq_fisher \
  --output /tmp/fisher-bridge.proof.txt
```

### 4B. Combined Semantic Snapshot

Use this when you want one packet containing semantic blocks plus a bridge
query.

```bash
lake script run semanticSnapshot \
  lean/InfoGeometry/Canonical/FisherVolumeBridge.lean \
  /tmp/fisher-bridge.snapshot.json \
  --bridge-method getProofState \
  --line 47 \
  --character 2 \
  --proof-fast \
  --timeout 120
```

### 4C. Warm Interactive Session

Use this for repeated proof-state or declaration-value queries on one file.

Start the session:

```bash
lake script run proofSession \
  lean/InfoGeometry/Canonical/FisherVolumeBridge.lean \
  --skip-wait-for-diagnostics \
  --prewarm-decl-name InfoGeometry.Canonical.FisherVolumeBridge.action_hessian_eq_fisher \
  --prewarm-pretty-print-value
```

Then send JSON lines such as:

```json
{"id":1,"method":"getDeclValue","declName":"InfoGeometry.Canonical.FisherVolumeBridge.action_hessian_eq_fisher"}
{"id":2,"method":"getProofState","line":47,"character":2}
{"id":3,"method":"didChange","text":"...full file text...","waitForDiagnostics":false}
{"id":4,"method":"reloadFromDisk","waitForDiagnostics":false}
{"id":99,"method":"close"}
```

Use the warm session when you want low-latency patch/query loops.

## Trust Order

When surfaces disagree, trust in this order:

1. Lean source
2. `lean/InfoGeometry/Audit.lean`
3. `artifacts/dag/*`
4. managed reports regenerated by `dagReports`
5. docs and older reference-memory notes

## Freshness Rule

Treat `reports/dag/*` as current only if both are true:

- `lake script run dagRefresh` has completed successfully
- `lake script run dagReports` has completed successfully

Use `lake script run dagDoctor` as the final freshness check.

The target healthy state is:

```text
Summary: ok=17 warn=0 fail=0
```

## Practical Default

For most tool work, do not improvise. Use exactly this:

```bash
lake script run dagAll
```

For most changed Lean work, use exactly this:

```bash
lake script run changedVerify
```

For proof-state work on one file, do not improvise. Use exactly this:

```bash
lake script run proofSession <file> --skip-wait-for-diagnostics
```

Then query the warm session with JSON.
