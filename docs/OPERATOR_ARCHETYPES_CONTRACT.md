# Operator archetypes: theorem contract

## Input and scope

Source: the user attachment `Pasted text(20261027-142754).txt`, received
2026-10-27. Its five proposed layers are associative star algebra, inner
derivations, idempotent geometry, cyclic trace, and unitary/Kraus maps.
The implementation works on full `Matrix n n ℂ` for arbitrary finite `n`.
Operators are not assumed diagonal, scalar, or pairwise commuting.

Baseline: `nickgou-nuke/info-geometry-lean`, `main`,
`b143075bbf27e75860a1011e04423a0f227b7c41`.
Toolchain and dependencies remain at the repository pins: Lean 4.34.1 and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Grounded owners

* `Core.IdempotentCartan`: `evenPart`, `oddPart`, `projection_laws`,
  `multiplication_rules`, `odd_eq_double_commutator`, `odd_zero_iff_commute`.
  These are ring-polynomial operations, already defined over any ring.
* `Core.PeirceTangent`: the equation `p*x + x*p = x`, its commutator
  reconstruction, and self-adjoint tangent/skew-adjoint generator equivalence.
* `Quantum.ChoiCompletePositivity`: `Choi.krausMap V`, a native complex-linear
  map with value `∑ i, V i * X * star (V i)`.
* `Modular.Choi`: `krausChannel` is definitionally that same map.
* `Quantum.KrausAmplificationCP`: `amplification` on arbitrary finite ancillary
  index `r`, and `amplification_krausChannel_posSemidef`.
* Native Mathlib: `Matrix`, `IsStarProjection`, `unitary`,
  `Unitary.conjStarAlgAut`, `LinearMap`, the associative Lie bracket,
  `Matrix.PosSemidef`, and cyclic trace.

No replacement definitions for commutators, orthogonal projections, unitaries,
Kraus maps, or amplification are introduced. The canonical checkout contains
other agents' staged boundary-duality work; it is neither modified nor imported.

## Intended new claims

1. State the different bilinear trace and sesquilinear Hilbert--Schmidt
   adjoint identities for the native matrix Lie bracket.
2. Bundle the existing Peirce operations into native complex-linear maps.
3. Derive their trace-pairing self-adjointness, orthogonal images, and exact
   Pythagorean trace identity when `p` is a native star projection.
4. Derive the operator-valued Kadison defect
   `E (star A * A) - star (E A) * E A = star (O A) * O A`, its positivity,
   and equality exactly when `Commute p A`.
5. Identify `E` with the existing Kraus map on `p, 1-p`; transport the
   existing all-size amplification positivity theorem. Prove unitality,
   trace preservation, the bimodule property, and covariance under the
   native unitary star-algebra automorphism.
6. Prove concrete nondiagonal noncommuting matrix examples, including failure
   of positivity of `O` and failure of multiplicativity of a complete Kraus map.

## Semantic corrections

The dependency relation is a branching proof dependency order, not an asserted
unique chain and not a homotopy. It will be extracted from constants occurring
in the checked declarations' types and values.

`Tr(A B)` and `Tr(star A * B)` are different pairings. For the first,
`ad H` is skew; for the second its adjoint is `ad (star H)`.
The Peirce odd part is a tangent-equation projector. No curvature, manifold,
connection, adiabatic theorem, or physical dynamical law is asserted.
Finite complete positivity is positivity at every finite matrix amplification;
it is already supplied by the existing owner, not inferred from trace alone.
The pinching channel's block-diagonal range need not be commutative; the
arbitrary input matrices still inhabit the full noncommutative algebra.

## Verification contract

Compile the full selected repository-source import closure against unchanged
pins, sequentially under `/tmp/info-geometry-build.lock`. Inspect every
declaration owned by the new modules, including generated declarations and
transitive axioms; allow only `propext`, `Classical.choice`, and `Quot.sound`.
Run the repository proof-proxy and semantic-vacuity gates and independent
mathematical and acceptance reviews. Do not claim a whole-repository build
from a scoped source-closure check. Verification results will be recorded
after the checks finish.
