# Infra Tools

This directory contains the maintained infrastructure entrypoints for the
repository.

Use these scripts for:
- authoritative declaration-DAG refresh under `artifacts/dag/`
- blueprint tag refresh and LeanArchitect preparation
- locked build execution
- causal-order reporting, theorem-surface classification, full and filtered NetworkX graph exports, and `InfoGeometry.All` coverage classification

Canonical entrypoints:
- [refresh_decl_graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/refresh_decl_graph.py)
- [refresh_blueprint_tags.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/refresh_blueprint_tags.py)
- [run_locked_lake_build.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/run_locked_lake_build.py)
- [generate_causal_report.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_causal_report.py)
- [classify_missing_all.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/classify_missing_all.py)
- [generate_theorem_surface_index.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_theorem_surface_index.py)
- [plot_decl_graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/plot_decl_graph.py)
- [generate_source_sink_compression.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_source_sink_compression.py)
- [select_openclaw_target.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/select_openclaw_target.py)

Rule:
- for full or umbrella builds, use the locked build wrapper here
- do not start concurrent `lake build` jobs from different terminals or MCP sessions

Top-level `tools/*.py` entrypoints remain as compatibility wrappers, but this
directory is the canonical maintained surface.

Outputs from `plot_decl_graph.py` include the full declaration/module graphs, the filtered theorem-surface frontier graphs, a dedicated top-20 frontier hotspot view, and a weighted frontier burn-down ranking under `reports/dag/`.

`generate_source_sink_compression.py` adds the missing incidence layer:
- atomic truth: declaration DAG
- generation layer: source bundles -> sink theorems
- hydrated readability: module carriers with path multiplicity, motif signatures, and compression potential
