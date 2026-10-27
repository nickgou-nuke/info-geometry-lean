# Rectangular Peirce–Drazin formalization

Source: user attachment `Pasted text(20261027-140818).txt`, received 2026-10-27.
Intake SHA-256: `11183ae1f29cd7b1b3b3f4c439e274e7a6a4501fa08d43c71061f5ae529487a4`.
The operative instruction is to extract exact noncommutative operator algebra
and geometry, with complete proofs and no scalar or diagonal replacement.
Risk: R2, finite matrix representation using existing algebraic owners.

## Corrections to the intake

1. For finite square complex matrices, `Q * K = 1` implies `K * Q = 1`.
   A proper retract therefore uses `K : Matrix n m R` and `Q : Matrix m n R`.
   The full corner embedding is injective and nonunital, not a scalar model.
2. A Peirce decomposition does not imply nilpotence of either corner.
   The uploaded `CoreNilpotentSplit` and `DrazinResolution` omit the nilpotence
   needed by their names. They are not introduced into the repository.
3. A general Drazin inverse satisfies `D * A * D = D`; it need not satisfy
   `A * D * A = A`. Reflexive inner inverses and Drazin inverses are distinct.
4. The lifted spectral projector is `K * (A * D) * Q`; it is generally different
   from the retract support `K * Q`.
5. Nilpotence at exponent zero forces the ambient matrix algebra to be trivial.
   Positive-power transport through a nonunital map does not extend to exponent zero.

## Owners and exact carrier

The new declarations use full `Matrix n n R` algebras over arbitrary rings,
rectangular matrix multiplication, native `NonUnitalRingHom`,
`IsIdempotentElem`, `LinearMap.range`, `LinearMap.ker`, `IsCompl`, and submodule
inclusion. Commutative coefficients are used for the native range/kernel API;
the resulting matrix algebra is not assumed commutative.

`Core/PeirceDecomposition.lean` owns the four-corner decomposition and routing
laws. `Core/PeirceGrading.lean` and `Core/FinitePeirceMatrix.lean` already supply
more general native submodule decompositions. They are not copied.
`QuantumContext/DrazinSpectralKernel.lean` owns the existing Drazin predicate
and spectral projector. The new lift constructs all three of its equations.
`Canonical/DrazinPowerBoundary.lean` already supplies the residual-nilpotence
criterion for commuting outer inverses; it is not repackaged here.

No commutativity is assumed between arbitrary ambient matrices. In the final
compression theorem, commutation with the specified idempotent is the explicit
invariant-splitting condition. For the lift, the products between the embedded
operator and complement vanish as consequences of `Q * N = 0` and `N * K = 0`.

## Dependency order

These are source-level proof dependencies, not physical time or a claimed
compiler-extracted graph. Their transitive closure orders the declarations.
Independent branches are not assigned invented causal arrows.

- Rectangular retract equations → idempotent support; multiplicative corner map.
- Multiplicative corner map → injectivity and positive-power transport.
- Idempotent support + native linear-map owners → range/kernel complementarity
  and the actual submodule-order criterion `range_le_iff`.
- Matrix rank inequalities → properness when `card m < card n`.
- Native adjoint reversal → adjoint covariance of the corner map.
- Corner multiplication + annihilation equations → positive-power expansion.
- Positive-power expansion + an inner Drazin witness + explicit nilpotence →
  `isDrazinInverse_lift`, with bound `k + r + 1` (not asserted minimal).
- Existing Peirce reconstruction + support commutation → compressed splitting.
- Compressed splitting + the lift → `isDrazinInverse_of_retract`.

## Verification

`[kernel_verified]` All 28 new theorem declarations compile in the focused,
locked check on [run 40541898577](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40541898577),
job `122322190975`. Source head: `f1cdba6fe04fb61900d0cd2dbf74702bfc05c6f4`,
checked as a PR merge into `b143075bbf27e75860a1011e04423a0f227b7c41`.

The command is `bash scripts/quality/check-rectangular-peirce.sh`. It uses official
Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) and the repository-pinned
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The three existing dependency
modules, three new theorem modules, and audit module compile serially, with
fresh project oleans and the pinned mathlib cache. No Lean warnings remain.

The all-declaration axiom gate reports `AXIOM_AUDIT_PASS: 28 declarations`.
Every report contains only `propext`, `Classical.choice`, and `Quot.sound`.
There are no placeholders, custom axioms, unsafe declarations, or native-decide
proof shortcuts in the new sources. The staged proof-proxy gate passes.

The semantic-vacuity gate reports zero errors and four short-proof warnings.
These are the definitional computation `cornerHom_apply`, the unit image
`cornerHom_one`, adjoint covariance `cornerHom_conjTranspose`, and the derived
annihilation identity `complement_mul_lift`. Each is an explicit computation
used by, or describing, the actual corner map; none assumes its own conclusion.
The independent semantic audit accepts the matrix scope and explicit hypotheses.

Verified source SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `Algebra/RectangularRetract.lean` | `e7023ea0de736d7f3510e1a5c8f415cd7ddbacc0ad1b6cdafa214c359260317e` |
| `QuantumContext/RectangularDrazinLift.lean` | `0137485c7223dadaf0b9634342361aa8518ac742e1596fec88636b6bb0f666af` |
| `QuantumContext/RectangularPeirceDrazin.lean` | `a1749d933f5459640d3abb425252941ec0fca86807762695e12b216e4f231d40` |
| `QuantumContext/RectangularPeirceDrazinAudit.lean` | `87c41a2972115a7fa483fc5d9a56be37e3b9c854f13b9c922f68fd3128eea57a` |

`[accepted_limited_scope]` Verification covers this import closure, not a full
root Lake build or all repository CI. The root manifest and dependency pins are
unchanged. No theorem asserts minimal Drazin index, automatic nilpotence,
physical equivalence, or a formal `PartialOrder` on declaration names. The
implemented order-theoretic statement is the native submodule inclusion
criterion `range_le_iff`; the declaration dependency order above is documentation.
