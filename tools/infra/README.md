# Infra Tools

This directory contains the maintained DAG, reporting, and build orchestration entrypoints.
The source of architectural truth is no longer purely Python-side: the native grammar lives in:
- [Architecture.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)

The infra layer exists to preserve memory and turn a large formal repository back into an auditable working surface after context has been lost.
Its purpose is to:
- externalize dependency and ownership state from Lean into stable artifacts
- check that adjacent translators and coherence files behave like actual morphism carriers
- expose theorem-surface burden, representation-depth legality, and process-flow pressure
- give CI and humans reproducible structural evidence for the next code-reading pass

It is not here to replace source reading or to legislate mathematical truth from Python alone.

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
- `generate_structural_fibers.py`
- `generate_semantic_quotient.py`
- `generate_projection_coloring.py`
- `select_openclaw_target.py`
- `canonical_policy_lint.py`

Stable spine supplements:
- `check_representation_depth.py`
- `generate_representation_depth_graph.py`

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
- causal/ownership shape
  - `generate_source_sink_compression.py`
  - `generate_causal_report.py`
  - `check_bipartite_bleed.py`
  - `generate_structural_dedup.py`
  - `generate_structural_fibers.py`
  - `generate_semantic_quotient.py`
  - `generate_projection_coloring.py`
- representation-depth grammar
  - `check_representation_depth.py`
  - `generate_representation_depth_graph.py`
- process-flow and coherence pressure
  - `lean/DAG/ProcessFlowExport.lean`
  - `generate_process_flow_report.py`

## Authoritative Inputs

Public authoritative DAG inputs live under [artifacts/dag](/home/goutev/LEAN4/info-geometry-lean/artifacts/dag):
- `full_graph.json`
- `index/decls.jsonl`
- `index/edges.jsonl`
- `structural-topology.json`
- `source-sink-bipartite.json`

Derived readable outputs live under [reports/dag](/home/goutev/LEAN4/info-geometry-lean/reports/dag).

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
