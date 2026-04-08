# Tooling Overview

The tooling surface is now split between:
- Lean-native enforcement under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
- exported graph and reporting helpers under `lean/DAG/` and `tools/`

The tooling exists to make the repository recoverable when local context is gone.
It is the maintained memory and audit surface for a theory that is distributed across many representation files.
Its purpose is to recover owner order, transport structure, coherence pressure, and wrapper burden quickly enough that direct code reading can start in the right place.

The maintained tooling surface is split into three directories and one planner package:
- [tools/infra/README.md](infra/README.md)
- [tools/frontier/README.md](frontier/README.md)
- [tools/docs/README.md](docs/README.md)
- `tools/planner/`

The maintained top-level standalone modules are:
- `pathing.py`
- `build_lock.py`
- `theorem_significance.py`
- `check_vacuity_policy.py`
- `vacuity_planner.py`
- `vacuity_policy_config.py`

Many other top-level `tools/*.py` files are compatibility wrappers that forward
to maintained subdirectory entrypoints. The current status map lives in
[docs/RepositoryMemoryMap.md](../docs/RepositoryMemoryMap.md).

### Top-level Support And Compatibility Modules

| File | Purpose |
|------|---------|
| `pathing.py` | Canonical path resolution for DAG artifacts (`default_decl_graph_file()` → `artifacts/dag/full_graph.json`, `default_decl_index_dir()` → `artifacts/dag/index/`); falls back to `.build/` for incremental builds |
| `graph.py` | Legacy compatibility shim routing old consumers to `archive/legacy/scripts/graph.py` |

All infra scripts use `pathing.py` to resolve artifact locations.

## Current Anchor Query

When local context is gone, the first theorem-growth corridor the tooling should help recover is:
- `PositiveMeasure -> Projective.Normalize -> PositiveRayCore -> RelativePotentialCore -> RelativePotentialCountBridge -> RelativeSurprisalOperatorLift`

That corridor is now a validated example of the intended workflow: use the tools to recover the rooted owner order, then read the owner files and grow the theory upward from the seed rather than backward from facade surfaces.

## Current Split

### `tools/infra`
Graph refresh, causal and theorem-surface reports, representation-depth summaries, process-flow reports, visualization (SVG/GraphML), and locked build orchestration.

### `tools/frontier`
Semantic block export and heavy-file frontier workflows.

### `tools/docs`
Documentation refresh helpers for generated doc surfaces.

## Integration with Lean DAG

Python never touches Lean internals directly. The integration is:
1. `tools/infra/refresh_decl_graph.py` prebuilds with `run_locked_lake_build.py` and invokes `lake env dagIndexer` (fallback: `lake env lean --run ...`)
2. The Lean indexer writes canonical JSON artifacts to `artifacts/dag/`
3. Downstream Python scripts consume those artifacts for reports, visualization, and linting
4. `tools/pathing.py` provides the single source of truth for artifact paths with fallback semantics

## Trust Order

If documentation about tooling disagrees, trust:
1. Lean source under `lean/InfoGeometry/Meta/` and [Audit.lean](../lean/InfoGeometry/Audit.lean)
2. the scripts under `tools/infra/`, `tools/frontier/`, and `tools/docs/`
3. the corresponding READMEs
4. older wrapper prose

Tooling should summarize the theory's morphisms and debt.
It should not invent ontology that is absent from the code.
