# Infra Tools

This directory contains the maintained DAG, reporting, and build orchestration entrypoints.
The source of architectural truth is no longer purely Python-side: the native grammar lives in:
- [Architecture.lean](../../lean/InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](../../lean/InfoGeometry/Audit.lean)

For maintained-vs-compatibility status across the whole tooling tree, see
[docs/RepositoryMemoryMap.md](../../docs/RepositoryMemoryMap.md).

The infra layer exists to preserve memory and turn a large formal repository back into an auditable working surface after context has been lost.
Its purpose is to:
- externalize dependency and ownership state from Lean into stable artifacts
- check that adjacent translators and coherence files behave like actual morphism carriers
- expose theorem-surface burden, representation-depth legality, and process-flow pressure
- give CI and humans reproducible structural evidence for the next code-reading pass

It is not here to replace source reading or to legislate mathematical truth from Python alone.

## Current Anchor Corridor

The current benchmark corridor for the infra layer is:
- `PositiveMeasure -> Projective.Normalize -> PositiveRayCore -> RelativePotentialCore -> RelativePotentialCountBridge -> RelativeSurprisalOperatorLift`

The infra reports should make four facts recoverable about that corridor:
- the root is representative/count ownership, not a high bridge facade
- normalization debt is owned first as `representativeMassShift`
- the count specialization consumes that ownership as `countMassShift`
- the operator branch ends in `relativeModularHamiltonian_sub_countMassShift_cocycle`, so the cocycle survives averaging instead of being recomputed heuristically

## Managed Operator Surface

Checked-in DAG policy now lives in [dag-toolchain.json](../../dag-toolchain.json).
The preferred operator entrypoints are:
- `lake script run dagStatus`
- `lake script run dagRefresh`
- `lake script run dagReports`
- `lake script run dagDoctor`
- `lake script run dagAll`
- `lake script run changedVerify`
- `lake script run bilingualSpineReport`

These are thin wrappers over the current Python corridor. `dagReports` also sets a repo-local Matplotlib cache under `.artifacts/matplotlib` so managed report runs do not depend on a writable home-directory config path. The underlying script lane remains maintained, but the pinned config and authoritative status surface now live above it.
The current managed report sequence keeps the theorem-surface index, bilingual RedLine spine report, source-sink compression, causal coverage report, theorem-significance report, sorry-equivalence report, NetworkX graph exports, and replacement-frontier outputs in sync with the authoritative DAG artifacts.
`bilingualSpineReport` can also emit per-module docstring stubs with reference seeds via `--stub-out-dir reports/dag/bilingual-docstring-stubs`.
The managed lane also records timing sidecars for the last authoritative refresh (`artifacts/dag/index/indexer-timing.json`) and the last managed report run (`artifacts/dag/report-timing.json`), which `dagStatus` and `dagDoctor` surface as operator-facing performance summaries.

For the exact operator runbook, including when to use the managed lane, the raw
repair lane, the depth-tag lane, and the process-flow lane, see
[docs/ToolingMethodology.md](../../docs/ToolingMethodology.md).
For the compressed operator surface, see
[docs/OperatorQuickstart.md](../../docs/OperatorQuickstart.md) and
[docs/DAGTroubleshooting.md](../../docs/DAGTroubleshooting.md).

The first authoritative Lake facet experiment is also available:
- `lake build :dagMeta`
- `lake build :dagArtifactsManifest`

It currently delegates to the same managed refresh lane underneath and exists to validate stronger dependency semantics on `artifacts/dag/index/meta.json` without changing the user-facing operator path.
The manifest-style facet writes `artifacts/dag/index/manifest.json`, which is a single small stamp for the whole authoritative refresh set (`meta.json`, `full_graph.json`, `structural-topology.json`) plus coverage/leakage sidecar state.

## Canonical Entrypoints

Main DAG refresh and report path:
- `refresh_decl_graph.py`
- `refresh_blueprint_tags.py`
- `reports/generate_bilingual_spine_report.py`
- `run_locked_lake_build.py`
- `build_changed_lean.py`
- `generate_theorem_surface_index.py`
- `generate_hypothesis_debt_report.py`
- `generate_source_sink_compression.py`
- `generate_causal_report.py`
- `check_bipartite_bleed.py`
- `generate_structural_dedup.py`
- `generate_structural_dictionary.py`
- `generate_structural_fibers.py`
- `generate_semantic_quotient.py`
- `generate_projection_coloring.py`
- `select_openclaw_target.py`
- `canonical_policy_lint.py`
- `agentic_policy_lint.py`
- `generate_replacement_frontier.py`
- `classify_missing_all.py`

Stable spine supplements:
- `check_representation_depth.py`
- `generate_representation_depth_graph.py`

Visualization and I/O:
- `plot_decl_graph.py`
- `representation_depth_io.py`

Process-flow supplements:
- `lean/DAG/ProcessFlowExport.lean`
- `generate_process_flow_report.py`

## Tool Families

Use the infra tools by role, not as one undifferentiated report pile:

- build/orchestration
  - `run_locked_lake_build.py`
  - `build_changed_lean.py` (incremental owner-module builds from git-changed Lean files; avoids umbrella rebuild loops by default)
- declaration graph refresh
  - `refresh_decl_graph.py`
  - `refresh_blueprint_tags.py`
- theorem-surface and canonical burden
  - `generate_theorem_surface_index.py`
  - `generate_hypothesis_debt_report.py` (ranks theorem/lemma surfaces by hypothesis/interface debt; defaults to synthesis capstones and emits top-20 JSON/Markdown)
  - `canonical_policy_lint.py`
  - `agentic_policy_lint.py` (enforces SOUL/HEARTBEAT/PUBLISH policy files, symbol-first protocol linkage, and runtime two-key publish gate settings)
  - `generate_replacement_frontier.py` (cross-references surface index, DAG, depth tags, and vacuity scores to rank replacement candidates)
- causal/ownership shape
  - `generate_source_sink_compression.py`
  - `generate_causal_report.py`
  - `check_bipartite_bleed.py`
  - `generate_structural_dedup.py`
  - `generate_structural_fibers.py`
  - `generate_semantic_quotient.py`
  - `generate_projection_coloring.py`
- apex-local obstruction diagnostics
  - `causal_cone_spectrum.py` (SCC-condensed causal cones, shells, binding witnesses, masses)
  - `apex_defect_profile.py` (structured obstruction dossiers per apex)
  - `graph_hodge_spectrum.py` (global spectral/Hodge report on undirected shadow)
- representation-depth grammar
  - `check_representation_depth.py`
  - `generate_representation_depth_graph.py`
  - `representation_depth_io.py` (shared I/O: loads depth indices, Lean tags JSON, interval labels)
- visualization
  - `plot_decl_graph.py` (NetworkX GraphML, SVG, burndown charts; frontier category coloring)
- classification and structural
  - `classify_missing_all.py`
  - `generate_structural_dictionary.py`
- process-flow and coherence pressure
  - `lean/DAG/ProcessFlowExport.lean`
  - `generate_process_flow_report.py`

## Authoritative Inputs

Public authoritative DAG inputs live under [artifacts/dag](../../artifacts/dag):
- `full_graph.json`
- `index/decls.jsonl`
- `index/edges.jsonl`
- `index/edge-leakage.json`
- `index/morphisms.jsonl`
- `index/types.jsonl`
- `structural-topology.json`
- `source-sink-bipartite.json`
- `representation-depth-tags.json`
- `process-flow/` — Lean-authoritative exports: `flow-edges`, `process-events`, `lawful-path-candidates`, `defects`; Python-derived supplements: `flow-cocycles`, `comparison-candidates`

Derived readable outputs live under [reports/dag](../../reports/dag).

## Maintained Refresh Order

For normal use, prefer the managed exact sequence from
[docs/ToolingMethodology.md](../../docs/ToolingMethodology.md):

```bash
lake script run dagAll
```

Expanded managed sequence:

```bash
lake script run dagStatus
lake script run dagRefresh
lake script run dagReports
lake script run dagDoctor
```

For active theorem/refactor work, prefer incremental owner builds between managed runs:

```bash
lake script run changedVerify --dry-run
lake script run changedVerify
```

This intentionally skips umbrella modules like `*.All` unless `--allow-umbrella` is passed.

Use the raw order below only when narrowing or repairing a tool failure.

Strict-coverage raw runbook (fails if graph coverage is partial):

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
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

Partial-coverage diagnostic variant (continues when coverage is known partial):

```bash
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json --allow-partial-coverage
python3 tools/infra/dag_status.py
python3 tools/infra/dag_doctor.py
```

Process-flow refresh (Lean export + Python derivation):

```bash
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

The Lean export writes the constitutive process-flow lane:
`flow-edges`, `process-events`, `lawful-path-candidates`, `defects`.
The Python step derives:
`flow-cocycles`, `comparison-candidates`, and the process-flow defect report.
This step can be heavy on large snapshots; run it after the core DAG reports are stable.

Full end-to-end audit snapshot (build + DAG + doctor + debt surfaces):

```bash
lake build -R
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
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

Interpretation notes:
- keep `canonical_policy_lint.py` as a hard signal; do not suppress failures in CI
- `dag_doctor.py` coverage-policy failure can coexist with fresh artifacts
- `generate_process_flow_report.py` is often the slowest step on large snapshots

Run the native audit before trusting the representation-depth reports. Run the main sequence sequentially. Do not trust `reports/dag/*` as current until the main sequence has finished.

## Operational Rules

- use `run_locked_lake_build.py` for umbrella builds
- `refresh_decl_graph.py` now prebuilds `dagIndexer` for `--run-mode exe` and `DAG.Indexer` for `--run-mode run`, together with the import root, under the build lock
- do not run concurrent umbrella builds
- do not hand-edit `artifacts/dag/*`
- read code before acting on hotspot heuristics
- use the representation-depth reports as rendered summaries of the Lean-native grammar, not as the grammar itself
- use process-flow reports as local transport/coherence evidence, not as proof substitutes
- treat infra outputs as context-restoration tools: they should tell you what to read next, not what to believe without reading it

## Policy Surface

`canonical_policy_lint.py` enforces repository policy around:
- proposition-valued wrapper surfaces
- theorem-class tagging in canonical files
- suspect theorem burden in stable canonical owners
- reopening of structural hotspot and shell debt tracked by the refreshed artifacts

It is a source-level policy pass. Generated or internal declarations without a
valid source line are not part of its public-theorem scan.
