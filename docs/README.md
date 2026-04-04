# Documentation Map

This directory is a map, not the kernel of truth for live repo state.

## Documentation Classes

### Operational docs
Use these for current structure and workflow:
- [README.md](../README.md)
- [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
- [Installation.md](../Installation.md)
- [NEWCOMER_PATH.md](../NEWCOMER_PATH.md)
- [ModuleMap.md](ModuleMap.md)
- [OperationalIntent.md](OperationalIntent.md)
- [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
- [lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean)
- [lean/DAG/README.md](../lean/DAG/README.md)
- [tools/README.md](../tools/README.md)
- [tools/infra/README.md](../tools/infra/README.md)

### Conceptual docs
These explain the stable mathematical picture and owner order:
- [Theory.md](Theory.md)
- [causal_apex_binding.md](causal_apex_binding.md)
- other markdown files in `docs/`

Conceptual docs should explain the codebase, not override it.
OperationalIntent is the short statement of why the repo and its tooling are structured this way.

### Reference memory docs
These remain useful, but they are not the first operational authority:
- [FORMALIZATION_PROTOCOL.md](../FORMALIZATION_PROTOCOL.md)
- [LLM_FRONTIER_PROTOCOL.md](../LLM_FRONTIER_PROTOCOL.md)
- [LLM_DEBT_PROTOCOL.md](../LLM_DEBT_PROTOCOL.md)
- [SELF_OPTIMIZATION_PROTOCOL.md](../SELF_OPTIMIZATION_PROTOCOL.md)

If a document is not linked from this page or [RepositoryMemoryMap.md](RepositoryMemoryMap.md),
re-audit it against current code before using it as live policy.

### Generated docs and reports
These are derived surfaces:
- [docs/auto/index.md](auto/index.md)
- [reports/dag/](../reports/dag)
- [artifacts/dag/](../artifacts/dag)

Generated surfaces should be refreshed, not hand-curated.

## Recommended Read Path

1. [README.md](../README.md)
2. [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
3. [ModuleMap.md](ModuleMap.md)
4. [OperationalIntent.md](OperationalIntent.md)
5. [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
6. [Theory.md](Theory.md)
7. the current anchor corridor:
   [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean),
   [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean),
   [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean),
   [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean),
   [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean),
   [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)
8. [lean/DAG/README.md](../lean/DAG/README.md)
9. [tools/infra/README.md](../tools/infra/README.md)
10. [causal_apex_binding.md](causal_apex_binding.md) for the condensed-DAG apex/binding overlay proposal
11. live reports under [reports/dag/](../reports/dag)
