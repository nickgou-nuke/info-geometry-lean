# Tooling Hierarchy

This directory contains the Python-side orchestration for the InfoGeometry DAG,
audit, frontier, and optimization workflows.

Canonical maintained entrypoints now live under:
- [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md)
- [tools/frontier/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/README.md)
- [tools/docs/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/docs/README.md)

Top-level `tools/*.py` entrypoints remain as compatibility wrappers for now, but
the subdirectories above are the supported canonical paths.

Read this hierarchy in order:

1. [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
- repository-wide proof policy, trusted artifact placement, and current-vs-legacy split

2. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
- Lean-side graph engine, export lanes, and authoritative declaration/semantic workflows

3. `tools/README.md` (this file)
- Python orchestration hierarchy and script status

## Current Hierarchy

### Level 1: Authoritative declaration-DAG pipeline

Use this for causal order, coverage, rooted partial-order analysis, and native structural topology.

Inputs:
- `artifacts/dag/full_graph.json`
- `artifacts/dag/index/decls.jsonl`
- `artifacts/dag/structural-topology.json`
- `artifacts/dag/source-sink-bipartite.json`

Authoritative refresh path:
- [refresh_decl_graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/refresh_decl_graph.py)
- [Indexer.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/Indexer.lean)

Primary Python consumers:
- [generate_causal_report.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_causal_report.py)
- [select_openclaw_target.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/select_openclaw_target.py)
- [classify_missing_all.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/classify_missing_all.py)
- [generate_theorem_surface_index.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_theorem_surface_index.py)
- [plot_decl_graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/plot_decl_graph.py)
- [generate_source_sink_compression.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_source_sink_compression.py)
- [check_bipartite_bleed.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/check_bipartite_bleed.py)
- [generate_structural_dedup.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_structural_dedup.py)
- [generate_structural_fibers.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_structural_fibers.py)

Use this lane when the question is:
- what is the root set?
- what is the true causal order?
- which declaration-bearing files are still outside `InfoGeometry.All`?
- how do I open the current declaration DAG as a NetworkX/GraphML graph?
- how do I isolate only the hypothesis/package/surrogate frontier?
- how do I recover stable condensation components, strict dominators, and canonical root witness paths?
- how do I recover source bundles, repeated path motifs, and compression carriers instead of only adjacency?
- which hydrated carriers are structurally bleeding across native component closures?
- which theorem surfaces are really the same semantic packet under different packaging?
- where does the bulk source-sink packet split into independent corridor fibers before hydrated projection?
- what is the next OpenClaw target once coverage gaps are closed?

### Level 2: Authoritative blueprint / LeanArchitect pipeline

Use this for theorem-level blueprint coverage and exact LeanArchitect extraction.

Inputs:
- `artifacts/dag/index/decls.jsonl`

Authoritative refresh path:
- [refresh_blueprint_tags.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/refresh_blueprint_tags.py)
- [auto_blueprints.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/auto_blueprints.lean)
- [BlueprintTags.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/BlueprintTags.lean)

Primary build consumers:
- `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags`
- `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprint`
- `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprintJson`

Use this lane when the question is:
- which declarations are blueprint-covered?
- what exact TeX / JSON does LeanArchitect emit for the current theory surface?
- how do I separate exhaustive formal node extraction from curated mathematical exposition?

### Level 3: Authoritative semantic-block pipeline

Use this for heavy-file semantic structure and frontier discovery.

Authoritative exporter:
- [semantic_block_export.py](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/semantic_block_export.py)

Primary consumers:
- [skynet_v2.py](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/skynet_v2.py)
- [generate_auto_docs.py](/home/goutev/LEAN4/info-geometry-lean/tools/docs/generate_auto_docs.py)
- [update_repo_docs.py](/home/goutev/LEAN4/info-geometry-lean/tools/docs/update_repo_docs.py)

Use this lane when the question is:
- what is the semantic frontier around a heavy theorem?
- which semantic blocks bridge KK -> AnalyticalIndex -> GrandSynthesis?
- what is the human-facing block structure of a capstone file?

### Level 4: Current audit/report generators

These are current and supported, but they are report generators rather than graph roots.

- [generate_surrogate_index.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_surrogate_index.py)
- [generate_vacuity_index.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_vacuity_index.py)
- [generate_bridge_thinness_index.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_bridge_thinness_index.py)
- [generate_unification_index.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_unification_index.py)
- [generate_bridge_candidates.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_bridge_candidates.py)
- [generate_debt_candidates.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_debt_candidates.py)
- [generate_llm_frontier_prompts.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_llm_frontier_prompts.py)
- [generate_llm_debt_prompts.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_llm_debt_prompts.py)
- [generate_self_optimization_report.py](/home/goutev/LEAN4/info-geometry-lean/tools/generate_self_optimization_report.py)

### Level 5: Current quarantine/optimization lane

These are current, but operational rather than canonical.

- [run_optimization_cycle.py](/home/goutev/LEAN4/info-geometry-lean/tools/run_optimization_cycle.py)
- [proof_driver.py](/home/goutev/LEAN4/info-geometry-lean/tools/proof_driver.py)
- [failure_correction_driver.py](/home/goutev/LEAN4/info-geometry-lean/tools/failure_correction_driver.py)
- [build_lock.py](/home/goutev/LEAN4/info-geometry-lean/tools/build_lock.py)

### Level 6: Compatibility / limited / legacy surfaces

These still exist for older consumers or ad hoc inspection, but they are not the canonical causal-order source of truth.

- [graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/graph.py)
  Compatibility shim that re-exports the archived NetworkX wrapper from `archive/legacy/scripts/graph.py`.
- any workflow centered on `docs-map/graph.json` or `archive/legacy/scripts/make_graph.py`
  Archived compatibility only. Do not treat it as the authoritative causal substrate.

## Practical Rule

If there is disagreement between layers:
- trust the declaration DAG in `artifacts/dag/` for causal order
- trust semantic block JSONs in `reports/dag/*.semantic-block.stdlib.json` for human-facing heavy-file structure
- regenerate derived markdown/JSON reports instead of editing them by hand
