# Documentation Map

This directory is mixed:

- a small set of hand-maintained operational docs
- a larger set of conceptual, synthesis, backlog, and reference-memory notes
- one generated doc surface under `docs/auto/`

Lean source is still the truth surface. These docs exist to help orientation, not to override code.

## Foundational Theory

The repository's core theoretical axiom is **Goutev’s Principle of Absolute 
Relativity of Measurement**:

- [Goutevs_Principle.md](Goutevs_Principle.md) — The formal manifesto.
- [LIBER_NOVUS_MATH.md](LIBER_NOVUS_MATH.md) — The "Red Book": Analytical Psychology methodology for mathematical development.
- [WORKBENCH.md](WORKBENCH.md) — The practical playbook for Socratic/Alchemical discovery.
- [black_books/](black_books/) — The "Black Books": Raw intuitive exploration (Scorpio). Includes the Thermodynamics of Joy, Sisyphian Perseverance, Eureka Tunneling, and the Gravitational Well.
- [black_books/08_the_agentic_caretaker.md](black_books/08_the_agentic_caretaker.md) — The essay naming the repo agent as architect, creator, and caretaker under the law of the kernel.
- [black_books/09_science_after_coding.md](black_books/09_science_after_coding.md) — The essay on exploration by dialogue, Jungian elicitation, Socratic distillation, and formal handoff to Lean.
- [Theory.md](Theory.md) — How the principle maps to the repo presentations.
- [Theory_Highway_Prognosis.md](Theory_Highway_Prognosis.md) — The project's roadmap and trajectory.
- [SEMANTIC_POTENTIAL.md](SEMANTIC_POTENTIAL.md) — The "Scorpio & Virgo" multi-agent generative engine.

## What Is Current

Use these first when you want the current repo state:

- [README.md](../README.md)
- [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
- [OperationalIntent.md](OperationalIntent.md)
- [Theory.md](Theory.md)
- [ModuleMap.md](ModuleMap.md)
- [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
- [lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean)
- [lean/DAG/README.md](../lean/DAG/README.md)
- [tools/README.md](../tools/README.md)
- [tools/infra/README.md](../tools/infra/README.md)

These are the maintained hand-written entry surfaces.

## What Is Generated

Only the following doc surface under `docs/` is script-owned:

- [docs/auto/index.md](auto/index.md)

Its owning scripts are:

- [tools/docs/generate_auto_docs.py](../tools/docs/generate_auto_docs.py)
- [tools/docs/update_repo_docs.py](../tools/docs/update_repo_docs.py)

Related generated artifacts also live under:

- [reports/dag/](../reports/dag/)
- [artifacts/dag/](../artifacts/dag/)

Do not hand-edit generated surfaces unless the generator itself is being repaired.

## What Is Reference Memory

Everything else in `docs/` should be treated as reference memory unless this page
or [RepositoryMemoryMap.md](RepositoryMemoryMap.md) explicitly promotes it.

That includes:

- synthesis notes such as `welding_theorem_synthesis.md`, `*_synthesis.md`
- diagnostics and backlog notes such as `analytic_closure_backlog.md` and `apex_*.md`
- niche conceptual overlays such as `causal_apex_binding.md`
- glossaries and indexes such as `keyword_index.md` and `lawful-flow-glossary.md`

These files can still be useful, but they must be re-audited against Lean source
before being used as live policy.

## Recommended Read Path

For current repo structure:

1. [README.md](../README.md)
2. [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
3. [OperationalIntent.md](OperationalIntent.md)
4. [Theory.md](Theory.md)
5. [ModuleMap.md](ModuleMap.md)
6. [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean)
7. [tools/infra/README.md](../tools/infra/README.md)

For the current count/projective/operator trunk:

1. [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
2. [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
3. [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
4. [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
5. [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
6. [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

For the corrected phase-space/generalized-metric trunk:

1. [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
2. [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
3. [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
4. [PhaseSpaceGeneralizedMetricChiralityBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean)
5. [PhaseSpacePolarizedBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean)
6. [PhaseSpaceRecompositionBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean)

## Rule

If a doc and Lean source disagree, trust Lean source.

## Consistency Pass (2026-04-07)

Repository-wide checks were run across all files under `docs/`:

- markdown links resolve;
- referenced Lean file paths resolve; and
- stale path references were corrected where needed.

Files updated in this pass:

- `docs/red_line_synthesis.md`
- `docs/lean_compiler_service.md`
- `docs/keyword_index.md`
