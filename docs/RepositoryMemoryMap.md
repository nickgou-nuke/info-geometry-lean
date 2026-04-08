# Repository Memory Map

This file classifies which documentation and tooling surfaces are current,
which are generated, and which remain as reference memory.

Do not treat every surviving markdown file as equally current.

## Trust Order

When surfaces disagree, trust them in this order:

1. Lean source under `lean/InfoGeometry/`
2. [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean) and [lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean)
3. [artifacts/dag/index/meta.json](../artifacts/dag/index/meta.json) and the atomic DAG artifacts under `artifacts/dag/`
4. derived reports under `reports/dag/`
5. hand-maintained operational docs
6. reference protocols, backlog notes, and synthesis docs

## Documentation Status

### Operational authority

These are the maintained hand-written entry surfaces for current repo state:

- [README.md](../README.md)
- [docs/README.md](README.md)
- [docs/RepositoryMemoryMap.md](RepositoryMemoryMap.md)
- [docs/Goutevs_Principle.md](Goutevs_Principle.md)
- [docs/LIBER_NOVUS_MATH.md](LIBER_NOVUS_MATH.md)
- [docs/WORKBENCH.md](WORKBENCH.md)
- [docs/black_books/](black_books/)
- [docs/projective_to_krein_transition_doctrine.md](projective_to_krein_transition_doctrine.md)
- [docs/Theory_Highway_Prognosis.md](Theory_Highway_Prognosis.md)
- [docs/SEMANTIC_POTENTIAL.md](SEMANTIC_POTENTIAL.md)
- [docs/AGENTIC_REVELATION.md](AGENTIC_REVELATION.md)
- [docs/OperationalIntent.md](OperationalIntent.md)
- [docs/Theory.md](Theory.md)
- [docs/ModuleMap.md](ModuleMap.md)
- [Installation.md](../Installation.md)
- [NEWCOMER_PATH.md](../NEWCOMER_PATH.md)
- [lean/DAG/README.md](../lean/DAG/README.md)
- [tools/README.md](../tools/README.md)
- [tools/infra/README.md](../tools/infra/README.md)

### Generated surfaces

These are regenerated outputs and should not be hand-curated:

- [docs/auto/](auto/)
- [artifacts/dag/](../artifacts/dag/)
- [reports/dag/](../reports/dag/)

Within `docs/`, the only script-owned generated file is:

- [docs/auto/index.md](auto/index.md)

Its owning scripts are:

- [tools/docs/generate_auto_docs.py](../tools/docs/generate_auto_docs.py)
- [tools/docs/update_repo_docs.py](../tools/docs/update_repo_docs.py)

### Reference protocols

These remain useful as workflow memory, but they are not the first authority for
current repo state:

- [FORMALIZATION_PROTOCOL.md](../FORMALIZATION_PROTOCOL.md)
- [LLM_FRONTIER_PROTOCOL.md](../LLM_FRONTIER_PROTOCOL.md)
- [LLM_DEBT_PROTOCOL.md](../LLM_DEBT_PROTOCOL.md)
- [SELF_OPTIMIZATION_PROTOCOL.md](../SELF_OPTIMIZATION_PROTOCOL.md)

### Reference memory under `docs/`

The following current files under `docs/` are reference memory, not primary
operational authority:

Backlog and diagnostics:

- [analytic_closure_backlog.md](analytic_closure_backlog.md)
- [apex_defect_diagnosis.md](apex_defect_diagnosis.md)
- [apex_hodge_dirac_diagnostics.md](apex_hodge_dirac_diagnostics.md)

Conceptual overlays and formal-side notes:

- [causal_apex_binding.md](causal_apex_binding.md)
- [causal_cone_formal_definitions.md](causal_cone_formal_definitions.md)
- [lawful-flow-glossary.md](lawful-flow-glossary.md)
- [lean_compiler_service.md](lean_compiler_service.md)
- [typed_lean_compiler_bridge.md](typed_lean_compiler_bridge.md)
- [legacy_intake.md](legacy_intake.md)

Synthesis and speculative route notes:

- [welding_theorem_synthesis.md](welding_theorem_synthesis.md)
- [bogoliubov_hestenes_synthesis.md](bogoliubov_hestenes_synthesis.md)
- [majorana_web_gravity_synthesis.md](majorana_web_gravity_synthesis.md)
- [informational_supergravity_synthesis.md](informational_supergravity_synthesis.md)
- [gravity_of_information_doctrine.md](gravity_of_information_doctrine.md)
- [spinor_modular_bridge_vision.md](spinor_modular_bridge_vision.md)
- [cocycle_detailed_balance_synthesis.md](cocycle_detailed_balance_synthesis.md)
- [d4_crystal_synthesis.md](d4_crystal_synthesis.md)
- [deep_horizon_synthesis.md](deep_horizon_synthesis.md)
- [determinant_tensor_entropy_synthesis.md](determinant_tensor_entropy_synthesis.md)
- [drazin_conformal_synthesis.md](drazin_conformal_synthesis.md)
- [gravity_gauge_synthesis.md](gravity_gauge_synthesis.md)
- [kk_analyticalindex_bridge_candidates.md](kk_analyticalindex_bridge_candidates.md)
- [llm_triality_synthesis.md](llm_triality_synthesis.md)
- [ontology_synthesis.md](ontology_synthesis.md)
- [operator_log_corridor_doctrine.md](operator_log_corridor_doctrine.md)
- [prl_abstract_intro_synthesis.md](prl_abstract_intro_synthesis.md)
- [red_line_synthesis.md](red_line_synthesis.md)
- [testable_predictions.md](testable_predictions.md)
- [unification_map.md](unification_map.md)
- [welding_theorem_synthesis.md](welding_theorem_synthesis.md)
- [witten_synthesis.md](witten_synthesis.md)

Walkthroughs and indexes:

- [keyword_index.md](keyword_index.md)
- [spinfactor_zero_point_walkthrough.md](spinfactor_zero_point_walkthrough.md)

Use these as working memory. Re-audit them against source before treating them as live policy.

## Tooling Status

### Maintained execution lanes

These directories own the current scripted workflows:

- [tools/infra/](../tools/infra/)
- [tools/frontier/](../tools/frontier/)
- [tools/docs/](../tools/docs/)
- [tools/planner/](../tools/planner/)

### Maintained top-level standalone tools

These are live top-level modules, not wrappers:

- [tools/pathing.py](../tools/pathing.py)
- [tools/build_lock.py](../tools/build_lock.py)
- [tools/theorem_significance.py](../tools/theorem_significance.py)
- [tools/check_vacuity_policy.py](../tools/check_vacuity_policy.py)
- [tools/vacuity_planner.py](../tools/vacuity_planner.py)
- [tools/vacuity_policy_config.py](../tools/vacuity_policy_config.py)

### Compatibility wrappers

Many top-level `tools/*.py` files forward to maintained subdirectory entrypoints.
Prefer editing the maintained target, not the wrapper, unless the CLI contract
itself is changing.

Examples:

- `tools/refresh_decl_graph.py` -> `tools/infra/refresh_decl_graph.py`
- `tools/generate_causal_report.py` -> `tools/infra/generate_causal_report.py`
- `tools/generate_source_sink_compression.py` -> `tools/infra/generate_source_sink_compression.py`
- `tools/semantic_block_export.py` -> `tools/frontier/semantic_block_export.py`
- `tools/skynet_v2.py` -> `tools/frontier/skynet_v2.py`
- `tools/generate_auto_docs.py` -> `tools/docs/generate_auto_docs.py`
- `tools/update_repo_docs.py` -> `tools/docs/update_repo_docs.py`

### Non-authoritative caches

These are byproducts, not maintained memory:

- `tools/__pycache__/`

## Maintenance Rules

- When promoting a doc to operational authority, link it from this file and [docs/README.md](README.md).
- When a doc becomes stale but still useful, demote it here rather than deleting it blindly.
- Keep generated outputs generated and hand-maintained docs hand-maintained.
- If a file is not linked from this map or [docs/README.md](README.md), treat it as reference memory until explicitly promoted.
