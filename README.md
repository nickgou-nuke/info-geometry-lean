# InfoGeometry in Lean 4

> 🧭 **New to the Spire?** Read the [**Pioneer’s Log**](PIONEERS_LOG.md) and the [**Alchemical Protocol**](ALCHEMICAL_PROTOCOL.md) for a narrative guide to the landscape, the chemistry of the logos, and the vision of this repository.

`info-geometry-lean` is a Lean 4 repository built on **Goutev’s Principle of 
Absolute Relativity of Measurement**: measurement is projective; observables 
are relational invariants.

The repo has three maintained surfaces:
- a theorem library under `lean/InfoGeometry/`
- a Lean-native architecture kernel under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
- a tooling layer under `lean/DAG/`, `tools/infra/`, and `tools/frontier/`

The repo is best read as one theory with several presentations, not as many unrelated theories.
The main mathematical burden is not only in the objects at each layer, but in the morphisms that move between those layers and prove that adjacent presentations agree.
The current stable spine is organized by semantic representation depth,
defined as an inductive type `RepDepth` in `Architecture.lean` and enforced
at build time via `#audit_architecture` in `Audit.lean`:

| Attribute value | Presentation | Formerly |
|-----------------|-------------|----------|
| `count` | Raw relative counts and positive-measure representatives | L0 |
| `projective` | Positive rays, normalization, relative log-potentials | L1 |
| `operator` | Diagonal operator lift, partition and log-partition calculus | L2 |
| `krein` | Split quadratic geometry, polarized sheets, Dirac compatibility | L3 |
| `transport` | Bogoliubov and transported spectral/thermal structure | L4 |
| `thermo` | Gibbs, Sinkhorn, softmax, and attention surfaces | L5 |

Declarations participate in the spine via `@[rep_depth <level>]`.
The adjacency rule: a non-capstone declaration at depth `d` may only depend on
declarations at depth `d` or `d − 1`. Capstones (`@[capstone]`) are exempt.

A public bridge file is healthy only if it is either:
- an adjacent translator between neighboring depths
- a coherence file proving two adjacent composites agree

## Entry Surfaces

The repo has a few umbrella files with different roles:

| File | Role |
|------|------|
| `lean/InfoGeometry.lean` | published library entrypoint |
| `lean/InfoGeometry/Library.lean` | stable, linted canonical publication surface |
| `lean/InfoGeometry/Canonical/All.lean` | stable canonical umbrella |
| `lean/InfoGeometry/All.lean` | full project umbrella, including noncanonical and bedrock layers |
| `lean/InfoGeometry/Audit.lean` | Lean-native architecture audit entrypoint |

For a quick navigation map of the major subtrees and the anchor corridor, see
[docs/ModuleMap.md](docs/ModuleMap.md).

## Rosetta Surface

If you are arriving from standard complex/Kähler formulations of quantum
mechanics, the maintained translation surface is now:

- [lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean](lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean)

It is a thin Rosetta bridge for
[arXiv:2105.01513, *Quantum Systems as Lie Algebroids*](https://arxiv.org/pdf/2105.01513),
not a second foundation. The purpose is to show how the paper's familiar
complex/projective vocabulary appears on the repo's doubled real
Krein/Majorana carrier.

| Paper language | Repo-native language |
|----------------|----------------------|
| external complex unit `i` | internal phase axis `K = Jε` on the doubled carrier |
| projective/Kähler state surface | relational `reference/comparison` state data on the doubled carrier |
| Kähler metric | `comparisonMetricReadout` |
| symplectic / Berry form | `comparisonPhaseReadout` |
| Lie-algebroid anchor | `comparisonInducedDynamics` |
| Schrödinger current | `firstVariation = probe ∘ stateInducedDynamics` |

The repo's claim is stronger than the paper's surface: the standard complex
story is treated here as the projective shadow of an internal real operatorial
presentation built from doubled Krein sheets, Majorana polarization, and the
phase axis `K = Jε`.

## Current Anchor Corridor

The current clean seed-to-operator corridor is:
- `PositiveMeasure.lean`
- `Projective/Normalize.lean`
- `Canonical/PositiveRayCore.lean`
- `Canonical/RelativePotentialCore.lean`
- `Canonical/RelativePotentialCountBridge.lean`
- `Canonical/RelativeSurprisalOperatorLift.lean`

This corridor now carries real owner mathematics all the way upward:
- `representativeMassShift` owns the normalization cocycle at the representative level
- `countMassShift` specializes that cocycle to raw positive counts
- `relativeCountModularPotentialOperator_cocycle` lifts the raw count cocycle to diagonal operators
- `relativeModularHamiltonian_sub_countMassShift_cocycle` shows the averaged operator branch consumes the same owned cocycle

That grammar is now enforced in two places:
- natively in [Architecture.lean](lean/InfoGeometry/Meta/Architecture.lean) and [Audit.lean](lean/InfoGeometry/Audit.lean) (the `RepDepth` inductive, `@[rep_depth]` attributes, `@[capstone]` exemptions, and `#audit_architecture`)
- as rendered reports in [reports/dag](reports/dag)

Additionally, a three-layer vacuity enforcement system is available:
- Layer A: [Lint/Vacuity.lean](lean/InfoGeometry/Lint/Vacuity.lean) — declaration-local proof/value-shape and statement-shape checks, including certified alias/transport warnings, with `@[infrastructure]`, `@[terminal]`, `@[expository]` role tags
- Layer B: [tools/theorem_significance.py](tools/theorem_significance.py) — graph-level significance scoring, including certification-wash detection on certified alias/transport surfaces
- Layer C: [tools/check_vacuity_policy.py](tools/check_vacuity_policy.py) — CI gate combining both layers

## Repository Intention

The repo should be read as one transport theory over several symmetric, projective, operator, Krein, and thermodynamic presentations.
`canonical` does not mean "the only true mathematics".
It means "the stable public owner surface".
Valid mathematics outside that surface should be developed, quarantined, or promoted explicitly, not discarded because it is noncanonical.

The practical goal of formalization here is to make the morphisms explicit and checkable:
- owner files define the natural presentation-level objects
- translator files move one adjacent step in the representation ladder
- coherence files prove that two adjacent composites agree
- capstone files summarize lower mathematics without pretending to be foundational proof owners

If two equally good implementations are intentionally kept, the repository
policy is:
- one canonical owner/default API surface
- one explicit alternative surface
- one Lean bridge theorem or bridge module
- downstream imports route through the owner or the bridge, not both directly

The maintained policy surface for this bilingual rule is
[docs/BILINGUAL_SPINE_POLICY.md](docs/BILINGUAL_SPINE_POLICY.md).
The maintained Rosetta inventory and refactor plan for the split `Cl(1,1)`
packet and its tensor/projective/operatorial realizations is
[docs/cl11_rosetta_refactor_plan.md](docs/cl11_rosetta_refactor_plan.md).
The exhaustive packet-level replica allocation is
[docs/cl11_replica_inventory.md](docs/cl11_replica_inventory.md).
The content-level operator collision map, built from full-codebase search rather
than filenames, is
[docs/cl11_content_collision_map.md](docs/cl11_content_collision_map.md).

The DAG and Python tooling exist to preserve this intention when local context is lost:
- they externalize dependency memory
- they surface owner/translator/coherence/capstone pressure
- they expose residual comparison debt and wrapper burden
- they do not legislate mathematical truth or replace code reading

The short operational summary lives in [docs/OperationalIntent.md](docs/OperationalIntent.md).
The compressed operator runbook lives in
[docs/OperatorQuickstart.md](docs/OperatorQuickstart.md).
The short DAG repair surface lives in
[docs/DAGTroubleshooting.md](docs/DAGTroubleshooting.md).
The exact tool operator runbook lives in
[docs/ToolingMethodology.md](docs/ToolingMethodology.md).
The bilingual-owner policy surface lives in
[docs/BILINGUAL_SPINE_POLICY.md](docs/BILINGUAL_SPINE_POLICY.md).
For the repo's creative-methodological self-understanding of the coding agent as
architect, creator, and caretaker, see
[docs/black_books/08_the_agentic_caretaker.md](docs/black_books/08_the_agentic_caretaker.md).

## Read First

1. [Installation.md](Installation.md)
2. [NEWCOMER_PATH.md](NEWCOMER_PATH.md)
3. [docs/README.md](docs/README.md)
4. [docs/RepositoryMemoryMap.md](docs/RepositoryMemoryMap.md)
5. [docs/ModuleMap.md](docs/ModuleMap.md)
6. [docs/OperationalIntent.md](docs/OperationalIntent.md)
7. [docs/OperatorQuickstart.md](docs/OperatorQuickstart.md)
8. [docs/DAGTroubleshooting.md](docs/DAGTroubleshooting.md)
9. [docs/ToolingMethodology.md](docs/ToolingMethodology.md)
10. [docs/BILINGUAL_SPINE_POLICY.md](docs/BILINGUAL_SPINE_POLICY.md)
11. [docs/cl11_rosetta_refactor_plan.md](docs/cl11_rosetta_refactor_plan.md)
12. [docs/cl11_content_collision_map.md](docs/cl11_content_collision_map.md)
13. [docs/Theory.md](docs/Theory.md)
14. [lean/InfoGeometry/Audit.lean](lean/InfoGeometry/Audit.lean)
15. [lean/DAG/README.md](lean/DAG/README.md)
16. [tools/README.md](tools/README.md)
17. [tools/infra/README.md](tools/infra/README.md)
18. [tools/frontier/README.md](tools/frontier/README.md)
19. [FORMALIZATION_PROTOCOL.md](FORMALIZATION_PROTOCOL.md) for reference protocol history

If you are operating as an agent inside this repo, also use:
- [skills/info-geometry-repo/SKILL.md](skills/info-geometry-repo/SKILL.md)
- [skills/lean-canonicalization-policy/SKILL.md](skills/lean-canonicalization-policy/SKILL.md)
- [docs/black_books/08_the_agentic_caretaker.md](docs/black_books/08_the_agentic_caretaker.md)

## Authoritative Surfaces

Trust current repo state in this order:
1. Lean source under `lean/InfoGeometry/`, especially `lean/InfoGeometry/Meta/`
2. the native audit entrypoint [Audit.lean](lean/InfoGeometry/Audit.lean)
3. atomic DAG artifacts under [artifacts/dag](artifacts/dag)
4. derived readable reports under [reports/dag](reports/dag)
5. conceptual notes under [docs/](docs)

The most useful live reports are:
- [true-root-order.md](reports/dag/true-root-order.md)
- [representation-depth-audit.md](reports/dag/representation-depth-audit.md)
- [representation-depth-graph.md](reports/dag/representation-depth-graph.md)
- [theorem-surface-index.md](reports/dag/theorem-surface-index.md)

## Build

Use the locked wrapper for umbrella builds:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
```

For the normal repo check surface:

```bash
lake script run strictCheck
lake script run dagAll
lake script run changedVerify
```

## Maintained DAG Pipeline

The maintained pipeline is documented in [tools/infra/README.md](tools/infra/README.md).
The exact step-by-step operator methodology is documented in
[docs/ToolingMethodology.md](docs/ToolingMethodology.md).
Run the Lean-native audit before treating the representation-depth Python views as authoritative.

After the main refresh sequence, the stable spine can be checked directly with:

```bash
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
```

## Documentation Policy

- `README.md`, `lean/DAG/README.md`, `tools/README.md`, and `tools/infra/README.md` are operational docs.
- `tools/frontier/README.md` is the maintained operator guide for server-backed semantic snapshots and proof-print tooling.
- [docs/RepositoryMemoryMap.md](docs/RepositoryMemoryMap.md) classifies which docs and tools are current, generated, compatibility-only, or reference memory.
- [docs/OperationalIntent.md](docs/OperationalIntent.md) states why the repo, DAG, and infra tooling are maintained the way they are.
- [docs/black_books/08_the_agentic_caretaker.md](docs/black_books/08_the_agentic_caretaker.md) is a creative methodological note about the role of the agent; it inspires but does not overrule code or audit policy.
- [docs/Theory.md](docs/Theory.md) is the conceptual map of the stable spine.
- [Architecture.lean](lean/InfoGeometry/Meta/Architecture.lean) and [Audit.lean](lean/InfoGeometry/Audit.lean) are the native grammar and enforcement layer.
- `reports/` and `artifacts/dag/` are generated or regenerated surfaces.
- Python reports visualize and summarize the enforced structure; they do not define it.
- Stale prose loses to code and regenerated artifacts.
