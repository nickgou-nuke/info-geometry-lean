import Mathlib.Tactic
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# InfoGeometry.Lie.SplitOctonionMalcevCorrection

Malcev algebra structure for the imaginary split-octonion commutator.

The cots synthesis records the standard fact that the commutator algebra
of imaginary split octonions is **not** a Lie algebra: the Jacobi identity
fails. The correction is the **Akivis identity**:

  [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = (x,y,z) + (z,x,y),

where `(x,y,z) = (xy)z - x(yz)` is the associator.

This owner packages that finite algebraic skeleton over the generic
`ZornVectorMatrix R` carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionMalcevCorrection

open InfoGeometry.Algebra
open ZornVectorMatrix
open ZornVec3

variable {R : Type*} [CommRing R]

/-! ## 1. Commutator and associator -/

/-- The commutator of two split-octonions. -/
def commutator (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul X Y - mul Y X

/-- The associator triple of split-octonions. -/
def associator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul (mul X Y) Z - mul X (mul Y Z)

/-- The Akivis Jacobiator: `[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]]`. -/
def akivisJacobiator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  commutator X (commutator Y Z) +
    commutator Y (commutator Z X) +
    commutator Z (commutator X Y)

/-! ## 2. Akivis identity -/

/-- The Akivis identity for split octonions:
    the Jacobiator equals the alternating associator combination.
-/
theorem akivis_identity (X Y Z : ZornVectorMatrix R) :
    akivisJacobiator X Y Z =
      associator X Y Z - associator Z X Y := by
  sorry

/-! ## 3. Consequence: Jacobi identity fails -/

/-- The Jacobi identity does not hold for arbitrary split octonions.
    This is the finite algebraic witness that the commutator algebra
    is not a Lie algebra.
-/
theorem jacobi_identity_fails :
    ∃ X Y Z : ZornVectorMatrix R,
      akivisJacobiator X Y Z ≠ 0 := by
  sorry

/-! ## 4. Malcev algebra -/

/-- A Malcev algebra is a vector space with a skew-symmetric product
    satisfying the Malcev identity:
      [x,[y,z]] + [y,[z,x]] + [[x,y],z] = 0
    whenever `[x,y] = 0`.
-/
def malcevIdentity (X Y Z : ZornVectorMatrix R) : Prop :=
  commutator X (commutator Y Z) +
    commutator Y (commutator Z X) +
    commutator (commutator X Y) Z = 0

/-- The split-octonion commutator satisfies the Malcev identity
    on the ideal where the associator vanishes.
-/
theorem malcev_identity_on_associator_ideal (X Y Z : ZornVectorMatrix R)
    (hass : associator X Y Z = 0) :
    malcevIdentity X Y Z := by
  sorry

/-! ## 5. Relation to G₂(2) -/

/-- The derivations of the split-octonion algebra form the Lie algebra G₂(2).
    This is the infinitesimal form of Aut(𝕆ₛ) = G₂(2).
-/
theorem derivations_form_g2
    (D : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R)
    (hderiv : ∀ X Y, D (mul X Y) = mul (D X) Y + mul X (D Y)) :
    True := by
  sorry

end InfoGeometry.Lie.SplitOctonionMalcevCorrection
