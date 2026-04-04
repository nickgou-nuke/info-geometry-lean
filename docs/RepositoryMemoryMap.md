# Repository Memory Map

This page classifies which documentation and tooling surfaces are current,
which are generated, and which remain in the repository as reference memory.

Keep old memory in git. Do not silently treat every surviving file as equally
current.

## Trust Order

When surfaces disagree, trust them in this order:

1. Lean source under `lean/InfoGeometry/`, especially `Meta/`, `Lint/`, and `Audit.lean`
2. `artifacts/dag/index/meta.json` and the atomic DAG artifacts under `artifacts/dag/`
3. derived reports under `reports/dag/`
4. operational docs and maintained tooling READMEs
5. reference protocols, backlogs, and historical notes

## Documentation Status

### Operational authority

These are the current hand-maintained entry surfaces:

- [README.md](../README.md)
- [docs/README.md](README.md)
- [docs/ModuleMap.md](ModuleMap.md)
- [docs/OperationalIntent.md](OperationalIntent.md)
- [Installation.md](../Installation.md)
- [NEWCOMER_PATH.md](../NEWCOMER_PATH.md)
- [lean/DAG/README.md](../lean/DAG/README.md)
- [tools/README.md](../tools/README.md)
- [tools/infra/README.md](../tools/infra/README.md)

### Reference protocols

These stay in the repo as working memory, but they are not the primary
operational authority for current repo state:

- [FORMALIZATION_PROTOCOL.md](../FORMALIZATION_PROTOCOL.md)
- [LLM_FRONTIER_PROTOCOL.md](../LLM_FRONTIER_PROTOCOL.md)
- [LLM_DEBT_PROTOCOL.md](../LLM_DEBT_PROTOCOL.md)
- [SELF_OPTIMIZATION_PROTOCOL.md](../SELF_OPTIMIZATION_PROTOCOL.md)

### Historical or index-style notes

These preserve earlier classifications, canopies, or backlog views. Use them as
reference memory and re-audit them against code before treating them as live
policy:

- [BRIDGE_THINNESS_INDEX.md](../BRIDGE_THINNESS_INDEX.md)
- [SURROGATE_INDEX.md](../SURROGATE_INDEX.md)
- [UNIFICATION_INDEX.md](../UNIFICATION_INDEX.md)
- [VACUITY_INDEX.md](../VACUITY_INDEX.md)
- [THEORY_CANOPY.md](../THEORY_CANOPY.md)
- [THEORY_CANOPY_RN_GAUGE.md](../THEORY_CANOPY_RN_GAUGE.md)
- [UNIVERSAL_VOLUME_STACK.md](../UNIVERSAL_VOLUME_STACK.md)
- [RELEASE_NOTES.md](../RELEASE_NOTES.md)

### Generated surfaces

Do not hand-curate these unless the owning generator is being repaired:

- [docs/auto/](auto/)
- [artifacts/dag/](../artifacts/dag/)
- [reports/dag/](../reports/dag/)

## Tooling Status

### Maintained execution lanes

These directories own the current scripted workflows:

- [tools/infra/](../tools/infra/)
- [tools/frontier/](../tools/frontier/)
- [tools/docs/](../tools/docs/)
- [tools/planner/](../tools/planner/)

### Maintained top-level standalone modules

These are not wrappers; they are live top-level modules:

- [tools/pathing.py](../tools/pathing.py)
- [tools/build_lock.py](../tools/build_lock.py)
- [tools/theorem_significance.py](../tools/theorem_significance.py)
- [tools/check_vacuity_policy.py](../tools/check_vacuity_policy.py)
- [tools/vacuity_planner.py](../tools/vacuity_planner.py)
- [tools/vacuity_policy_config.py](../tools/vacuity_policy_config.py)

### Compatibility wrappers

Many top-level `tools/*.py` files are intentionally thin wrappers that forward
to maintained subdirectory entrypoints. Examples include:

- `tools/refresh_decl_graph.py` -> `tools/infra/refresh_decl_graph.py`
- `tools/generate_causal_report.py` -> `tools/infra/generate_causal_report.py`
- `tools/generate_source_sink_compression.py` -> `tools/infra/generate_source_sink_compression.py`
- `tools/select_openclaw_target.py` -> `tools/infra/select_openclaw_target.py`
- `tools/semantic_block_export.py` -> `tools/frontier/semantic_block_export.py`
- `tools/skynet_v2.py` -> `tools/frontier/skynet_v2.py`
- `tools/generate_auto_docs.py` -> `tools/docs/generate_auto_docs.py`
- `tools/update_repo_docs.py` -> `tools/docs/update_repo_docs.py`

Prefer editing the maintained target, not the wrapper, unless the CLI contract
itself is changing.

### Non-authoritative generated caches

These are build/runtime byproducts, not maintained repo memory:

- `tools/__pycache__/`

## Maintenance Rules

- When adding a new operational doc, update this file and the nearest README
  surface that points to it.
- When retiring a doc or script, reclassify it here before moving or archiving
  it.
- Keep generated outputs generated and hand-maintained docs hand-maintained.
- If a file is not linked from this map or a primary README, treat it as
  reference memory until it is explicitly promoted.
