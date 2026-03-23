# Infra Tools

This directory contains the maintained infrastructure entrypoints for the
repository.

Use these scripts for:
- authoritative declaration-DAG refresh and native structural-topology export under `artifacts/dag/`
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
- [check_bipartite_bleed.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/check_bipartite_bleed.py)
- [generate_structural_dedup.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_structural_dedup.py)
- [generate_structural_fibers.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_structural_fibers.py)
- [select_openclaw_target.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/select_openclaw_target.py)

Rule:
- for full or umbrella builds, use the locked build wrapper here
- do not start concurrent `lake build` jobs from different terminals or MCP sessions

Top-level `tools/*.py` entrypoints remain as compatibility wrappers, but this
directory is the canonical maintained surface.

Outputs from `plot_decl_graph.py` include the full declaration/module graphs, the filtered theorem-surface frontier graphs, a dedicated top-20 frontier hotspot view, and a weighted frontier burn-down ranking under `reports/dag/`.

`refresh_decl_graph.py` now emits the full native declaration artifact family under `artifacts/dag/`:
- atomic truth: `full_graph.json` + `index/decls.jsonl`
- native structural topology: `structural-topology.json`

`generate_source_sink_compression.py` then adds the correspondence layer and emits the public artifact `artifacts/dag/source-sink-bipartite.json`:
- atomic truth: declaration DAG
- native structure: condensation ids, membership, dominators, and canonical root-witness paths
- generation layer: source bundles -> hydrated carriers
- hydrated readability: module carriers with path multiplicity, motif signatures, and compression potential

`check_bipartite_bleed.py` then checks pairwise anti-bleed directly on the native structural layer:
- support source: hydrated `native_component_ids`, with incidence fallback
- closure source: native `dependencyComponentIds` on the condensation DAG
- outputs: `reports/dag/structural-anti-bleed.{json,md}` and `reports/dag/structural-hotspots.{json,md}`

`generate_structural_dedup.py` then emits quotient candidates over the same native correspondence surface:
- `dedup_families`: sink-surface merge candidates with one packet and multiple packaged endpoints
- `shadow_relations`: source/transport/consumer reflections that share a packet but should not be merged
- `assumption_packet_reuse`: repeated bundle/motif packets that still feed multiple carriers or sinks
- outputs: `reports/dag/structural-dedup.{json,md}`

`generate_structural_fibers.py` then emits a packet-conditioned bulk fiber decomposition over the same native correspondence surface:
- `packet_fibers`: per-packet corridor strands with wrapper counts, role chains, and native corridor representatives
- `source_sink_fiber_groups`: grouped packet classes for one broad source family and one consumer family
- `sink_family_entanglements`: sink-side bulk entanglement where several packet corridors converge into one family
- outputs: `reports/dag/structural-fibers.{json,md}`

`select_openclaw_target.py` is now a thin operational selector over current coverage plus structural hotspots:
- uncovered declaration-bearing debt outside graph coverage outranks everything else
- otherwise the selector ranks the native structural-hotspots surface directly
- outputs: `reports/dag/openclaw-targets.{json,md}`
