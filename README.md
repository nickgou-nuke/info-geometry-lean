# InfoGeometry

Lean 4 / Mathlib research in information geometry, noncommutative operator
algebra, Clifford and Zorn constructions, categorical limits, and mathematical
physics. The project is a growing atlas of definitions, theorems, and explicit
comparisons developed through human–AI collaboration. Its research motivation
includes the spinorial *prima materia* program; the mathematical claims are the
statements in the Lean owners, with their actual hypotheses.

> Documentation source review: 2026-11-03, against
> [`214f7bcf733e`](https://github.com/nickgou-nuke/info-geometry-lean/commit/214f7bcf733eaf4720913bc2c082936f2480d3fc).
> This records source inspection, not a fresh full build. See the
> [audit and verification scope](docs/DOCUMENTATION_SOURCE_AUDIT_2026-11-03.md).

## Start here

| Purpose | Entry point |
|---|---|
| Set up and run a scoped check | [Getting started](docs/GETTING_STARTED.md) |
| Work as a coding or mathematical agent | [AGENTS.md](AGENTS.md), then the [canonical pipeline](docs/CANONICAL_AGENT_PIPELINE.md) |
| Find maintained guides and historical notes | [Documentation map](docs/README.md) |
| Explore the main Lean source | [lean/InfoGeometry/](lean/InfoGeometry/) and [InfoGeometry.All](lean/InfoGeometry/All.lean) |
| Trace operator-algebra owners | [OperatorAlgebra guide](lean/InfoGeometry/OperatorAlgebra/README.md) and [Peirce archetype ledger](docs/PEIRCE_OPERATOR_ARCHETYPES.md) |
| Search before proposing a construction | [Repository deep-search protocol](docs/REPO_DEEP_SEARCH_PROTOCOL.md) |

Search definitions, imports, instances, theorem statements, and consumers before
declaring a construction absent or identifying two mathematical presentations.
A module name or graph edge is a search aid. A formal comparison needs a stated
map and theorem on the relevant carriers.

## Representative mathematical results

These are selected entry points, not a completeness claim for their fields.
Each linked owner supplies the precise typeclasses and hypotheses.

| Area | Source-backed result | Owner |
|---|---|---|
| Peirce operator identities | Polynomial identities for an idempotent and arbitrary coefficients in an associative ring; A60 gives `τ₁ − τ₂ = −J − 2Σ` and `hProjSig(τ₁ − τ₂) = −16 V²Σ` | [CyclotomicBridge](lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CyclotomicBridge.lean) |
| Five-grade parity | The grade ±1 projectors sum to the odd Peirce component; the −2, 0, +2 projectors sum to the even component | [TripotentParity](lean/InfoGeometry/OperatorAlgebra/PeirceSpine/TripotentParity.lean) |
| Chiral zero-mode restriction | Projector intertwiners from anticommutation, and an involutive linear equivalence on the kernel under the stated tripotence and involution hypotheses | [TripotentChiralRestriction](lean/InfoGeometry/Core/TripotentChiralRestriction.lean) |
| Noncommutative RPA blocks | Exact block squaring and Hadamard intertwining retaining `a*b - b*a` and both ordered products | [OperatorRPABlock](lean/InfoGeometry/Physics/OperatorRPABlock.lean) |
| Operator-weighted phonons | Mode-sum commutators with the correction terms `[Ωᵢ, X] * numberOpᵢ` retained | [NuclearPhononOperatorWeights](lean/InfoGeometry/Physics/NuclearPhononOperatorWeights.lean) |
| Matrix towers | Full-matrix algebraic direct limits, stage maps, and an induced star structure | [Cl11TensorTowerLimit](lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean) |
| Categorical Zorn stages | A `ModuleCat ℂ` diagram and multiplication descended through its colimits | [ZornUHFColimit](lean/InfoGeometry/Categorical/ZornUHFColimit.lean) |
| Algebraic Cuntz shift | Injectivity of the existing canonical shift from a generator-level left inverse | [CuntzHoppingCantorLattice](lean/InfoGeometry/NCG/CuntzHoppingCantorLattice.lean) |
| Finite matrix Lax data | Trace cancellations and the determinant/nonzero-kernel equivalence | [LaxPairIsospectralMassGap](lean/InfoGeometry/NCG/LaxPairIsospectralMassGap.lean) |
| Split-octonion derivations | A stabilizer predicate and consequences for a parameterized derivation family | [GunaydinGurseySU3Stabilizer](lean/InfoGeometry/NCG/GunaydinGurseySU3Stabilizer.lean) |

For a concrete example, `OperatorRPABlock.rpa_square` retains the full operator
commutator when squaring `[[a,b],[-b,-a]]`. Its off-diagonal square vanishes
exactly when `a` and `b` commute. The corresponding chiral square contains the
distinct ordered products `(a-b)*(a+b)` and `(a+b)*(a-b)`.

The [CAR/Krein/projectivization note](README-CURRENT.md) and
[nuclear operator synthesis](docs/NUCLEAR_OPERATOR_SYNTHESIS.md) give additional
topic-specific maps and qualifications.

## Proof and interpretation boundaries

A Lean theorem establishes its formal conclusion under its stated assumptions.
Distinguish a definition, a conditional theorem, a constructed witness, and a
proved equivalence. An assumed interface needs an inhabitant before it can
serve as a realized model. A generator family needs independence and spanning
theorems before it is called a basis.

The repository develops compatible finite-stage systems, algebraic direct
limits, and categorical colimits. The category, bonding maps, and universal
property must be identified for each construction. Analytic completions,
positivity, spectral lower bounds, and physical continuum interpretations need
their own stated structures and proofs. In particular, a general-ring identity
with an operator-valued coefficient is not by itself a scalar spectral-gap
theorem.

New accepted proofs must satisfy the repository's source, compilation, and
axiom-review requirements. A source scan for proof holes, a successful module
build, and a declaration-level axiom audit are separate forms of evidence.
Intentional linter fixtures and recovered historical proofs have separate
roles; a blanket zero-debt claim about every tracked file would obscure them.
The [dated audit](docs/DOCUMENTATION_SOURCE_AUDIT_2026-11-03.md) records the exact
scope of the observed source scan and baseline CI results.

## Build and verify

Use the toolchain in [lean-toolchain](lean-toolchain), the dependency revisions
in [lake-manifest.json](lake-manifest.json), and the targets in
[lakefile.lean](lakefile.lean). The reviewed baseline pins Lean 4.34.1.
The [getting-started guide](docs/GETTING_STARTED.md) explains local path
dependencies and preflight checks.

From the checkout root, after checking that no other compilation is active:

```bash
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock InfoGeometry.Physics.OperatorRPABlock
```

Use `run_locked_lean.py` for individual files. A no-target invocation of the
build wrapper selects changed-owner mode; use `--all-default-targets` when an
all-default-target build is intended. `InfoGeometry.All` is an umbrella import,
and its build is a different coverage claim from all Lake default targets.

Preserve build caches and pinned dependencies. Never run `lake clean` or
delete `.lake` caches. See the [cache policy](WARNING_DO_NOT_RUN_CACHE.md) for
the existing wrapper's empty-cache hydration behavior and recovery boundaries.

## Graphs and optional research tooling

Declaration DAGs, LeanTrail, Arango queries, semantic retrieval, and symbolic
witnesses help locate owners and candidate comparisons. They do not replace
Lean proofs. Runtime endpoints, database selection, source revisions, and
ingestion freshness must be observed in the configured deployment.

The [canonical pipeline](docs/CANONICAL_AGENT_PIPELINE.md) distinguishes the
available Python commands from optional Pi, Hive, oracle, and Archon setup.
The [infra guide](tools/infra/README.md) describes the required local DAG
configuration. Historical graph counts are snapshots rather than current
repository invariants.

## Research history and use

This repository retains exploratory notes, historical reports, and proposed
mathematics alongside maintained source. Use the
[documentation map](docs/README.md) to distinguish their roles. The
[21 October 2026 research review](docs/reviews/2026-10-21-research-and-agent-accessibility.md)
is preserved as a historical assessment.

The maintainers do not provide technical support or commit to reviewing
unsolicited contributions. Readers are welcome to clone, fork, explore, and
develop their own extensions. Citation metadata is maintained in
[CITATION.cff](CITATION.cff).

## License

The repository is licensed under [Apache License 2.0](LICENSE).
