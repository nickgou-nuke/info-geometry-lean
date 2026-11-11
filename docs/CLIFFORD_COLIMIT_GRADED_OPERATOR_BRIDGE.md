# Clifford colimit graded operator action

## Provenance and scope

The motivating correction in the 2026-11-11 discussion is that the repository's
finite Clifford matrix stages embed into a genuine infinite algebraic direct
limit, and symmetry operators act on that whole algebra. The earlier emphasis
on finite-dimensional models did not describe this existing construction
adequately. This change connects its existing global parity to the existing
intrinsic graded-adjoint operator API.

The source baseline is `c143c264bc18bbf41d692be4e270b5b7f7405702`. Lean remains
`leanprover/lean4:v4.34.1`, with Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. This contract introduces no
dependency, toolchain, or ambient-carrier change.

## Existing owners

Let `B := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit`. Its stages are the
full real matrix algebras `Stage n`, of real dimension `4^n`, with the unital
embedding `A ↦ A ⊗ I₂`. The native `DirectLimit` identifies stage-tagged
elements when their images agree at a later common stage. Faithful stage maps
retain nonzero elements and noncommutative multiplication.

| Existing construction | Source and declarations |
| --- | --- |
| Actual quotient and universal ring lift | [DirectLimitSuperClosureLemmas](../lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean): `DirectLimitSuperClosure`, `directLimitOf`, `directLimitOf_injective`, `directLimitLift`, `directLimitLift_unique`, `directLimitEndomorphism`. |
| Real star-algebra carrier and faithful universal maps | [Cl11TensorTowerLimit](../lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean), [Cl11StarAlgebraColimit](../lean/InfoGeometry/Clifford/Cl11StarAlgebraColimit.lean): `ofStageStarAlgHom`, `ofStage_injective`, `lift`, `existsUnique_lift`. |
| Genuine infinite dimension | [Cl11ColimitDimension](../lean/InfoGeometry/Clifford/Cl11ColimitDimension.lean): `finrank_stage`, `not_finiteDimensional`, `ofStageStarAlgHom_not_surjective`. [Cl11StarAlgebraFiltration](../lean/InfoGeometry/Clifford/Cl11StarAlgebraFiltration.lean): `stageImage_strictMono`, `iSup_stageImage_eq_top`. |
| Global Clifford parity | [Cl11ChiralityTransport](../lean/InfoGeometry/Clifford/Cl11ChiralityTransport.lean): `stageChiralityConj_bond`, `limitChiralityConj`, `limitChiralityConj_ofStage`, `limitChiralityConj_involutive`, `limitChiralityConj_jwCreation`, `limitChiralityConj_jwAnnihilation`. |
| Generic graded operator laws | [IntrinsicGradedAdjoint](../lean/InfoGeometry/OperatorAlgebra/IntrinsicGradedAdjoint.lean): `gradedAdjoint`, `gradedAdjoint_leibniz`, `gradedAdjoint_parity_anticommutes`, `gradedAdjoint_square`, `gradedAdjoint_mixed`, `gradedAdjoint_conjugate`. |
| General-stage Jordan–Wigner input | [Cl55WittCAR](../lean/InfoGeometry/Canonical/Cl55WittCAR.lean): `globalChirality_transpose`, `creation_sq`, `annihilation_sq`, `same_site_car`. Despite its filename, these four declarations quantify over every stage. |

Every element of `B` has a finite-stage representative, and any finite
collection has representatives in a common stage. No single stage exhausts
`B`. This is an algebraic infinite-dimensional statement with an actual
quotient and compatibility maps.

## New owner contract

The focused consumer is
[Cl11GradedOperatorAction](../lean/InfoGeometry/Clifford/Cl11GradedOperatorAction.lean).
It imports `Cl11ChiralityTransport`, `Cl11StarAlgebraColimit`,
`IntrinsicGradedAdjoint`, and `Cl55WittCAR`; the existing mathematical owners
remain unchanged.

The missing connection is to package the already constructed global parity
as a native real algebra equivalence and use it in the existing operator API.
The construction must retain the underlying `limitChiralityConj` map, prove
real scalar compatibility and star preservation, and expose its stage
evaluation and involutivity. The native equivalences are
`stageChiralityAlgEquiv` and `limitChiralityAlgEquiv`; the corresponding
`stageChiralityConj_algebraMap`, `limitChiralityConj_algebraMap`,
`stageChiralityConj_star`, and `limitChiralityConj_star` lemmas supply the
compatibility proofs. It does not assume a new parity witness.

For this parity `θ`, the native operator is

```text
D_Q : Module.End ℝ B
D_Q(X) = Q * X - θ(X) * Q.
```

`gradedAdjoint_intertwines_ofStage` proves an equality of composed native
linear maps, whose pointwise content is

```text
D_(ofStage n Q) (ofStage n X)
  = ofStage n (Q * X - (Γ_n * X * Γ_n) * Q).
```

The generic owner already proves the graded Leibniz rule and, under the
explicit oddness hypothesis `θ Q = -Q`, the whole-algebra identities

```text
θ ∘ D_Q + D_Q ∘ θ = 0,
D_Q²(X) = (Q * Q) * X - X * (Q * Q).
```

It also owns simultaneous transport of parity and charge along algebra
equivalences. Fixed-parity transport requires its explicit intertwining
hypothesis. The new consumer reuses these results rather than reproving a
second general graded-operator theory.

For an embedded creation operator `C` and annihilation operator `A` at the
same site, the existing owners prove oddness, `C² = A² = 0`, and
`C*A + A*C = 1`. Their operator consequences are

```text
D_C² = 0,    D_A² = 0,    D_C*D_A + D_A*D_C = 0,
D_C(A) = 1, D_A(C) = 1.
```

These are statements about endomorphisms of the whole `B`. The same-site
readouts distinguish nonzero differentials from vacuous zero actions. The
public results are `gradedAdjoint_jwCreation_square`,
`gradedAdjoint_jwAnnihilation_square`, `gradedAdjoint_jw_same_site_anticommute`,
the two `gradedAdjoint_jwCreation_apply_jwAnnihilation` /
`gradedAdjoint_jwAnnihilation_apply_jwCreation` readouts, and the two
`gradedAdjoint_jwCreation_ne_zero` / `gradedAdjoint_jwAnnihilation_ne_zero`
theorems. These concrete readouts are part of the owner itself. The maintained
checker automatically enumerates and audits its declarations, including
private and generated auxiliaries, so no separate audit owner is introduced.

## Operator coherence, element coherence, and tails

The finite chirality elements satisfy
`Γ_(n+1) = Γ_n ⊗ gamma_chiral_base`, whereas the stage embedding sends
`Γ_n` to `Γ_n ⊗ I₂`. They are not a coherent element family. Their
conjugation operators are coherent, which is precisely what the existing
`matStageEmbed_globalChirality_conj` theorem proves. The resulting global
parity must be kept distinct from inner Peirce parity implemented by one
fixed finite-head element.

The existing [Cl11MatrixTowerTailShift](../lean/InfoGeometry/Canonical/Cl11MatrixTowerTailShift.lean)
owns `cl11MatrixLimit_tailRingEquiv` and its star compatibility. This is
cofinal reindexing of the full matrix stages: earlier elements survive in
later stages. It is different from intersecting tensor-tail subalgebras or
quotienting by an additional ideal. The new action uses the original `B` and
does not rebuild any of these carriers.

## Relation to coercivity and a physical mass gap

[LieJordanHodgeColimit.uniform_coercivity_at_limit](../lean/InfoGeometry/Canonical/LieJordanHodgeColimit.lean)
already transfers a uniform quadratic inequality to this actual algebraic
limit. Its inputs include a real-linear functional `tau` agreeing with every
normalized stage trace, compatible operators `H`, `P`, `Hn`, `Pn`, and a
single constant `gamma` for which the finite inequality holds at every
stage. The theorem does not construct that bound or require `gamma > 0`.
Its cofinal-tail counterpart is `uniform_coercivity_descends`.

[BoundedHomotopyCoercivity.coercivity_of_homotopy](../lean/InfoGeometry/OperatorAlgebra/BoundedHomotopyCoercivity.lean)
provides a second, dimension-independent route on an arbitrary real Hilbert
space. For bounded operators `d`, `h`, `P`, its hypotheses are
`d*h + h*d = 1-P`, `0 < C`, `‖h‖ ≤ C`, and `P x = 0`. It proves

```text
(1 / (2 * C^2)) * ‖x‖^2 ≤ ⟪x, (d*d† + d†*d) x⟫.
```

Here `d†` is the native Hilbert adjoint. The same owner's
`coercivity_of_form_domination` transfers that exact bound to a supplied
bounded `H` when `⟪x, (d*d† + d†*d) x⟫ ≤ ⟪x, H x⟫` holds for every `x`.
The new algebraic annihilation-charge action is not identified with `d†`:
the two graded actions above anticommute to zero, while the contracting
identity requires the separately constructed `h` and `P`.

Thus genuine infinity and dimension-independent coercivity interfaces are
already available. A physical Yang–Mills mass-gap claim still needs the
specified physical representation, selfadjoint Hamiltonian, and relevant
vacuum complement. The homotopy route requires constructing `h` with a
uniform bound and proving the physical form-domination hypothesis; a direct
uniform coercivity proof is another route. Passing to an unbounded represented
Hamiltonian or a continuum limit requires control of domains, kernels, and
limiting estimates. A
connection to a lattice or Osterwalder–Schrader construction needs explicit
maps and compatibility proofs. The existing
[TracialGNSDirichlet](../lean/InfoGeometry/OperatorAlgebra/TracialGNSDirichlet.lean)
provides a separate positive, selfadjoint bounded commutator-energy operator
on a completed GNS space under its tracial hypotheses; identifying the
chosen physical theory with that construction is a further obligation.

The theorem target is the algebraic graded-action connection. A physical
mass gap is outside this contract, and differential nilpotence is not a
positive spectral lower bound.

## Validation contract and present status

Independent source review accepted the mathematical scope of the new owner.
The placeholder audit, strict OpenGauss screener, and semantic-vacuity check
reported zero findings. The workflow's YAML, shell steps, and embedded Python
blocks parse, and its trigger paths cover the complete selected source closure.
These checks are separate from Lean compilation and declaration-axiom auditing.

The root Lake validation attempt stopped before project elaboration because
`external_refs/homotopy-hypothesis-lean4` was absent. The maintained scoped
checker below validates the selected source closure against the same pinned
toolchain and Mathlib without changing dependency pins or checker guards.

The focused workflow is
[cl11-graded-operators.yml](../.github/workflows/cl11-graded-operators.yml).
It reads the checked-in pins, initializes that exact Mathlib revision,
compiles the complete selected source closure under the shared build lock,
and recursively audits every declaration owned by the new module and the
existing infinite-dimensionality owner. The two targets have a 23-module
repository source closure at the baseline. It uses the maintained
`check_clifford_dirac.py` target override without modifying checker guards.
With the pinned Mathlib initialized at `../mathlib`, the scoped command is:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root ../mathlib \
  --output ../cl11-graded-report \
  --target InfoGeometry.Clifford.Cl11GradedOperatorAction \
  --target InfoGeometry.Clifford.Cl11ColimitDimension
```

Acceptance must explicitly check zero warnings in both selected owners, no reused
compilation rows, and only
`propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies.
Placeholder, strict screening, and semantic findings remain separately
reported checks. Source review and selected-module CI do not establish a
whole-repository build result.

Kernel acceptance is pending the focused compilation and axiom audit. The
first CI attempt stopped during checkout because upstream has an unrelated
gitlink without a URL in `.gitmodules`. The workflow now fetches the exact public
event revision without credentials or submodule traversal and checks its SHA
before reading any source or pin files.
The local scoped cache request has acquired the shared build lock and is
initializing the pinned native imports. The workflow uploads its
source-bound report and declaration audit so reviewers can inspect the
actual completion status. A successful focused run establishes only this
selected closure and these declarations, not a physical mass-gap theorem.
