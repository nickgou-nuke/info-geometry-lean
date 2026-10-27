# Rectangular Peirce–Drazin formalization

Source: user attachment `Pasted text(20261027-140818).txt`, received 2026-10-27.
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

Pending narrow compilation and independent QA. No kernel-verified claim is made
until compilation and the all-declaration axiom probe have executed.
