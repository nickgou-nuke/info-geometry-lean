# Tooling Methodology

This document is the exact operational methodology for running the maintained
tooling surfaces in this repository.

It is an operator runbook, not a conceptual note.

## Rules

- use Lake-managed entrypoints by default
- use raw Python or Lean commands only when repairing or narrowing a tool failure
- run the DAG lane sequentially, not in parallel
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

- `reports/dag/theorem-surface-index.{md,json}`
- `reports/dag/source-sink-compression.{md,json}`
- `reports/dag/true-root-order.{md,json}`
- `reports/theorem-significance.{md,json}`
- `reports/dag/sorry-equivalence.{md,json}`
- `reports/dag/declaration-networkx*.graphml`
- `reports/dag/module-networkx*.{graphml,svg,json}`
- `reports/dag/frontier-burndown.{md,json}`
- `reports/dag/replacement-frontier.{md,json}`

## Method 3: Raw DAG Repair

Use this only when the managed lane fails and you need to narrow the failing
stage.

### 3A. Authoritative DAG Core

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json
python3 tools/theorem_significance.py
python3 tools/infra/generate_sorry_equivalence.py
python3 tools/infra/plot_decl_graph.py
python3 tools/infra/generate_replacement_frontier.py
```

### 3B. Representation-Depth And Blueprint Refresh

Use this when the depth-tag lane or `BlueprintTags`-dependent reports matter.

```bash
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
```

### 3C. Extended Structural Diagnostics

Use these only when you intentionally need the extended derived layer.

```bash
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py
python3 tools/infra/causal_cone_spectrum.py
python3 tools/infra/apex_defect_profile.py
python3 tools/infra/graph_hodge_spectrum.py
```

### 3D. Process-Flow Lane

```bash
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

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
