# Zorn primal/dual operator contract — 2026-11-24

Base: `fe24e350b08fdea04f74c0748ef9fd9417c47529` (`main`).
Environment: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The three adjacent source files preserve the supplied attachments verbatim.
The second and third contain the same proposed Lean implementation.

## Exact carrier and reuse

Use the existing `InfoGeometry.Algebra.ZornVectorMatrix ℝ`, with fields
`a,v,w,b`, its actual cross-product multiplication, its existing real module,
and `ZornLeftCAR.leftMultiplication`. No second octonion carrier or associative
octonion instance is introduced. The associative target is `Module.End ℝ Z`.

Existing owners inspected:

- `Algebra/ZornVectorMatrix`: multiplication, conjugation, norm composition,
  alternativity, coordinate module.
- `Algebra/ZornLeftCAR`: injective linear left action, polarized alternativity,
  six-dimensional Clifford lift and nonmultiplicativity witness.
- `Algebra/ZornDerivationBridge`: `kirmse_left` derived from alternativity.
- `Algebra/ZornLeftGrading`, `ZornLeftParity`, `ZornLeftMajorana`: actual
  Peirce projectors and seven Clifford generator relations.
- `Lie/SplitOctonionCliffordAction`, `SplitOctonionCliffordNoninjective`:
  native seven-dimensional Clifford lift, domain dimension 128, target
  dimension 64, noninjectivity, kernel dimension at least 64. These already
  exist and are not reimplemented here.
- `Canonical/CartanSouriauCocycleGibbsCharacter`: actual finite affine
  moment-map ensemble and partition transformation.
- `Geometry/DualFlatKreinLegendreGraph`: native algebraic dual carrier,
  canonical symplectic pairing, and graph lift.

## Normalized theorem targets

1. Conjugate contraction for the genuine left action, both orders; explicit
   unit and `IsUnit (L z) ↔ norm z ≠ 0` over the real field.
2. Constructive linear equivalence from two independent four-vectors to the
   full Zorn carrier; norm equals the `(+---)` dual evaluation.
3. Primal/dual quasi-idempotence, with the full mixed anticommutator
   `p₀ L_X + x₀ L_P − η(x,p) I`.
4. Incidence as membership in the kernel of an actual linear functional,
   equivalent to noninvertibility. A geometric hyperplane requires nonzero
   dual vector; projective points require nonzero representatives.
5. Chiral half-sum and half-difference recovery, source-ordered volume
   operator `−I`, and exact nonassociativity witness `−2 q₇`.
6. Actual determinant of the represented eight-dimensional left action,
   `det(L_z) = norm(z)^4`, if the matrix-coordinate bridge and determinant
   proof are successfully checked.
7. Supporting Souriau attachment: algebraic affine action groupoid, inverse
   cocycle evaluation, finite negative-log Massieu midpoint concavity, and
   exact skew-graph coefficients on the existing primal/dual carrier.

## Rejected or corrected source claims

- The full Clifford representation cannot be faithful: 128-dimensional
  domain and 64-dimensional target. Injectivity of the vector-to-left-action
  map is a different statement.
- The Zorn norm on eight coordinates has signature `(4,4)`. Its imaginary
  restriction is `(3,4)`, and the Clifford form is its negative, `(4,3)`.
  The four-dimensional diagonal section has the Minkowski square.
- The generic mixed chiral anticommutator is not scalar.
- With `q₇=E22−E11`, the displayed associator witness is `−2q₇`.
- With `Ω=ν₂(ξ₁)−ν₁(ξ₂)+B(ξ₁,ξ₂)`, the graph `ν=c B(ξ,·)` pulls back to
  `(1−2c)B`. The negative graph gives `3B`, the positive graph gives `−B`.
- An algebraic action groupoid and a skew pairing do not establish a smooth
  symplectic groupoid, closedness, nondegeneracy, or multiplicativity.

## Dependency order

Zorn multiplication and alternativity → left action and conjugate contraction
→ invertibility criterion → primal/dual encoding and incidence.
Existing CAR and grading → chiral reconstruction and operator volume.
Coordinate intertwining plus actual matrix determinant → determinant incidence.
The Souriau groupoid/thermodynamic lane remains separate; no unproved map
between it and Zorn geometry is asserted.

## Validation policy and status

Implementation candidates require native Lean compilation, axiom audit,
placeholder scan, semantic review, and independent review. Compilation is
serialized with the maintained shared lock. The focused runner reads a pinned
dependency cache and writes only to this independent checkout. Root dependency
pins and Lake configuration remain unchanged. A focused check is not a
whole-repository build or a pre-push gate certificate.

Current status: source implementation and independent mathematical review
completed; native verification blocked. The first native compiler attempt was
terminated at an existing dependency without completing a module. The
single-thread retry was stopped while waiting for the shared build lock.
No native or axiom-audit acceptance is claimed. See `VALIDATION.md` for the
exact observed scope, reproduction command, and unfinished acceptance steps.
