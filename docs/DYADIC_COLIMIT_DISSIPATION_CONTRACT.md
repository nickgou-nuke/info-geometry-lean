# Dyadic colimit trace, dissipation, and shell symmetry

## Provenance and intent

This task extracts three algebraic targets from the supplied “ColimitClosure”
proposal. The unedited intake is preserved in
[`sources/colimit_closure_intake_20261112.txt`](sources/colimit_closure_intake_20261112.txt).
Its SHA-256 is
`0dae4430e81b637f53468bdb08fb611c4e33f1c8a15d76501fa44e2a521bd323`.
The intake is a proposal, not proof evidence. Its D5, D7 and D8 labels identify
the claims being evaluated; they do not certify the surrounding physical story.

The implementation builds on the actual matrix-amplification and categorical
colimit owners in PR #327, head
`d080548a26c4715ecb7b83d34f20fe2a4b5452cb`. This change is intended as a stacked
PR with base `feat/matrix-amplification-colimit`; it does not duplicate that
PR's diagram, direct-limit carrier, faithful inclusions or universal property.

The formal intent is to construct a compatible normalized trace, prove the
noncommutative polarized GKSL product defect, and construct a specific outer
ring automorphism of the algebraic colimit. The stages are full nested matrix
rings, with no restriction to diagonal or commuting matrices. These are
algebraic results. Completion, positivity of a state, quantum channels,
recurrence, modular flow and physical gauge quotients are separate targets.

## Existing owners and the missing implications

| Surface inspected | Existing result | Addition in this change |
| --- | --- | --- |
| `Categorical/MatrixAmplificationTower.lean` | Native recursive full matrix rings, scalar bonds, an actual categorical colimit, injective inclusions and finite/common-stage representatives | A compatible trace and a concrete non-inner automorphism on this same carrier |
| `Algebra/DirectLimitSuperClosureLemmas.lean` | Interval transitions, native `DirectLimit`, compatible maps and induced endomorphisms | Proved scalar preservation for the chosen bonds, and a self-inverse compatible family |
| `Algebra/PrimonColimitAlgebra.lean` | A real full-matrix colimit with a normalized linear trace | A coefficient-generic trace on the distinct recursive tower already owned by PR #327 |
| `Canonical/CuntzMatrixAlgebraicTraceFunctional.lean` | A complex algebraic star-colimit with a tracial functional | No replacement or claim that trace descent was previously absent |
| `Modular/GKSLDissipatorAlgebraic.lean` | Existing dissipator and finite Lindbladian; annihilation of `1` and star compatibility under explicit hypotheses | Polarized product-defect identities, skew-adjoint Hamiltonian cancellation, transport, and a star-ordered specialization |
| `Canonical/Cl11MatrixTowerTailShift.lean`, `Canonical/GrowingOnsiteMatrixHamiltonian.lean`, `Algebra/PrimonSuperalgebra.lean` | Related tail, fresh-shell and parity constructions on other carriers | A direct proof against every inner unit conjugation on PR #327's actual generic colimit |

The search covered the corresponding definitions, alternate terminology,
imports and consumers in `lean/` and `src/`, followed by reading the listed
owners. This is an owner-focused comparison, not a repository-wide absence
certificate. Native Mathlib source was inspected at the pinned revision for
`DirectLimit.Module.lift`, `DirectLimit.Algebra.of`, `Matrix.scalarAlgHom`,
`Matrix.compAlgEquiv`, ring-equivalence matrix transport and conjugation.

## D5: normalized trace on the existing dyadic colimit

Owner: `lean/InfoGeometry/Canonical/DyadicMatrixTraceColimit.lean`.

Let `K : Type` be a commutative ring. The carrier is exactly the existing
`MatrixAmplificationTower.Limit (Fin 2) (RingCat.of K)`, with stages
`A₀ = K`, `Aₙ₊₁ = Matrix (Fin 2) (Fin 2) Aₙ` and scalar-matrix bonds.
The recursive coefficients `Aₙ` are not assumed commutative. The implementation
adds native `Algebra K` structures and the scalar-preservation proofs for these
particular transitions. It does not assert an algebra-homomorphism instance
for arbitrary ring homomorphisms.

Under `[Invertible (2 : K)]`, define

\[
\tau_0(x)=x,\qquad
\tau_{n+1}(M)=2^{-1}\tau_n(\operatorname{tr} M).
\]

Acceptance targets:

- `stageTrace_bond`, `stageTrace_transition`: compatibility with the actual
  successor bonds and all interval maps.
- `stageTrace_one`, `stageTrace_mul_comm`: unitality and cyclicity. The cyclicity
  argument uses the preceding stage's tracial functional; it does not assume
  the matrix coefficients commute.
- `colimitTrace`: a native linear-map lift on the actual colimit carrier.
- `colimitTrace_inclusion`, `colimitTrace_one`, `colimitTrace_mul_comm`,
  `colimitTrace_commutator`, `colimitTrace_unique`: evaluation, unitality,
  cyclicity, commutator annihilation and uniqueness among linear functionals
  with the specified finite-stage restrictions.
- `stageTrace_not_multiplicative`, `colimitTrace_not_multiplicative`: under
  `[Nontrivial K]`, opposite off-diagonal units exhibit the obstruction to
  treating this trace as a ring homomorphism.
- `stageTrace_noncommuting_witness`: the same pair in the full matrix shell
  has unequal products in opposite orders, zero individual traces, and product
  trace `⅟(2 : K)`. Its noncommutation is proved using the existing matrix-unit
  commutator owner, imported directly.
- `stageThreeEquiv`: an explicit native algebra equivalence between the third
  stage and full matrices indexed by `Fin 2 × (Fin 2 × Fin 2)`. The index set has
  eight elements. This is an `8 × 8` matrix ring, not an eight-dimensional
  matrix algebra over `K`.

The functional is linear, not a `RingCat` morphism. Its lift therefore uses
`DirectLimit.Module.lift` on the same carrier. In the first matrix shell,
`τ(E₀₁) = τ(E₁₀) = 0` but `τ(E₀₁E₁₀) = 1/2`. No positivity, norm,
operator-algebra completion or physical anomaly theorem is included.
Inverting two supports every dyadic stage; it does not select a unique
supersymmetry parameter. Even a numerical condition `4 - N = 0` depends on
the coefficient characteristic.

## D7: polarized GKSL product defect

Owner: `lean/InfoGeometry/Modular/GKSLDissipationIdentity.lean`.

Reuse the existing definitions `dissipatorTerm`, `gkslDissipator` and
`totalLindbladian` on an arbitrary associative star ring. For a central,
self-adjoint element `h` with `2h = 1`, the existing one-jump dissipator is

\[
D_L(X)=L^*XL-h(L^*LX+XL^*L).
\]

The principal target keeps the multiplication order:

\[
D_L(X^*Y)-D_L(X)^*Y-X^*D_L(Y)=[L,X]^*[L,Y].
\]

Acceptance targets include the polarized and diagonal identities, the finite
sum identity, and the same identity for the existing total Lindbladian when
the Hamiltonian coefficient satisfies `star H = -H`. This explicit assumption
is what makes the inner-derivation star defect zero. Merely writing a product
`J * K` does not establish it.

The inverse-of-two specialization derives centrality and self-adjointness of
`⅟(2 : A)` from native Mathlib lemmas. Naturality uses native nonunital
maps `A →⋆ₙ+* B`: these polynomial identities do not require unit preservation.
The nonnegativity corollary adds the explicit `PartialOrder` and
`StarOrderedRing` assumptions needed for a sum of star squares.

These are identities for arbitrary elements, not just scalar or self-adjoint
inputs. They do not construct a completely positive semigroup, a time
parameter, a Kubo–Mori metric, a modular operator or a recurrence theorem.
This owner does not separately equip the dyadic colimit with a star operation
or construct a coherent family of jump operators on that carrier. The generic
star-ring identities and their transport laws are available for such a future
construction; they do not supply its compatibility data.
The algebraic tower relation

\[
\iota_{n+1}(\eta_n(x))=\iota_n(x)
\]

identifies the two representatives. Increasing a representative's stage
index is not dynamical motion in the colimit. A strictly growing tower alone
cannot exclude identity evolution or recurrence.

## D8: an actual outer shell automorphism

Owner: `lean/InfoGeometry/Categorical/MatrixAmplificationShellSymmetry.lean`.

Let `A : Type` be an arbitrary ring. Reuse the same full binary tower and its
actual colimit. Define `α₀ = id`. At stage `n + 1`, apply `αₙ` entrywise and
then conjugate by the fresh unit `diag(1,-1)`. This constructs native
`RingEquiv`s rather than assuming a compatible family of automorphisms.

Acceptance targets:

- `stageSymmetry_bond`: compatibility with the existing scalar bonds.
- `stageSymmetry_involutive`, `colimitSymmetryHom_involutive`: explicit inverses
  at finite stages and on the actual colimit.
- `colimitSymmetry`: a native ring equivalence of that colimit.
- `colimitSymmetry_inclusion`: the evaluation law on every finite stage.
- `freshShell_commute_inclusion`: the new `E₀₁` with coefficient `1` commutes
  with the whole preceding-stage image.
- `colimitSymmetry_freshShell`: the constructed symmetry negates this witness.
- `freshShell_ne_neg`: under `[Nontrivial A] [Invertible (2 : A)]`, faithfulness
  keeps the witness distinct from its negative.
- `colimitSymmetry_ne_inner`: for every colimit unit, this symmetry differs
  from the native ring equivalence given by conjugation by that unit.

For non-innerness, only the value of an arbitrary colimit unit needs a
finite-stage representative. Its conjugation fixes the next commuting shell
witness, while the constructed symmetry negates it. The proof does not assume
that a representative is already a unit in its finite stage. It does not
confuse inability to factor through a finite stage with outerness.

This proves a specific algebraic ring automorphism is outer. An arbitrary
compatible endomorphism need not be invertible; an arbitrary unit need not
implement a star-preserving map. No operator-algebraic outer classification,
bulk/asymptotic quotient, Elitzur theorem or physical gauge identification is
asserted.

## Compatibility of the trace and shell symmetry

Owner: `lean/InfoGeometry/Canonical/DyadicMatrixTraceShellSymmetry.lean`.

For a commutative coefficient ring with two invertible,
`stageTrace_stageSymmetry` and `colimitTrace_colimitSymmetry` establish that
the constructed symmetry preserves the normalized trace, first at every stage
and then on the actual colimit. No additional carrier or quotient is introduced.
Together with the D8 nontriviality hypothesis, this yields a specific
trace-preserving outer ring automorphism of the same algebraic colimit.

## Source-screening compatibility

The explicit matrix witness exposed two limitations in the staged source
screener. It treated the type ascription inside `[Invertible (2 : K)]` as an
ordinary term assumption, and it did not track the operators bound by a
top-level typed existential. Consequently it rejected the concrete
noncommuting pair even after the generic matrix witness owner was imported
directly.

The associated parser repair preserves the existing class, assumption,
taint and carrier checks. It recognizes a bounded native matrix existential
whose leading conjunct guarantees noncommutation. Conditional, disjunctive,
assumed, tainted and mismatched-carrier evidence must still be rejected.
`tests/test_opengauss_existential_witness.py` records these cases, and the
focused workflow also runs the existing screener, staged-gate, partial-commit
and diff-gate suites under the shared lock. These are parser regressions;
the Lean build and complete declaration audit supply the theorem checks.

## Validation and release record

The Lean and Mathlib pins are unchanged: Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Validation is in progress. Source authors prepared isolated candidates;
independent review checks the precise carrier and hypotheses; root integration
and kernel checks are separate. The focused verifier from PR #327 is used for
these owners, with the repository's shared build lock. It does not certify
the root project's optional path dependencies or unrelated targets.

The final record will report exact compilation, complete owned-declaration
axiom audit, staged proof gate and root pre-push outcomes. It must distinguish
successful focused checks from any root-package failure.
