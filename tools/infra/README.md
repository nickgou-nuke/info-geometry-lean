# Infra Tools

This directory contains the maintained DAG, reporting, and build orchestration entrypoints.
The source of architectural truth is no longer purely Python-side: the native grammar lives in:
- [Architecture.lean](../../lean/InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](../../lean/InfoGeometry/Audit.lean)

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

## Canonical Entrypoints

Main DAG refresh and report path:
- `refresh_decl_graph.py`
- `refresh_blueprint_tags.py`
- `run_locked_lake_build.py`
- `generate_theorem_surface_index.py`
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
- declaration graph refresh
  - `refresh_decl_graph.py`
  - `refresh_blueprint_tags.py`
- theorem-surface and canonical burden
  - `generate_theorem_surface_index.py`
  - `canonical_policy_lint.py`
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
- `index/morphisms.jsonl`
- `index/types.jsonl`
- `structural-topology.json`
- `source-sink-bipartite.json`
- `representation-depth-tags.json`
- `process-flow/` (flow-edges, process-events, flow-cocycles, comparison-candidates, lawful-path-candidates, defects)

Derived readable outputs live under [reports/dag](../../reports/dag).

## Maintained Refresh Order

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py
python3 tools/infra/generate_replacement_frontier.py
python3 tools/theorem_significance.py
python3 tools/infra/causal_cone_spectrum.py
python3 tools/infra/apex_defect_profile.py
python3 tools/infra/graph_hodge_spectrum.py
```

Supplemental stable-spine reports:

```bash
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
```

Process-flow refresh:

```bash
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

Run the native audit before trusting the representation-depth reports. Run the main sequence sequentially. Do not trust `reports/dag/*` as current until the main sequence has finished.

## Operational Rules

- use `run_locked_lake_build.py` for umbrella builds
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
