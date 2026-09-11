import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.AkivisLeftRegularBridge

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
theorem akivis_identity (X Y Z : ZornVectorMatrix ℝ) :
    akivisJacobiator X Y Z =
      -(6 : ℝ) • _root_.associator X Y Z := by
  change InfoGeometry.Algebra.rightNestedJacobiator X Y Z =
    -(6 : ℝ) • _root_.associator X Y Z
  rw [InfoGeometry.Algebra.rightNestedJacobiator_eq_neg,
    InfoGeometry.Algebra.zornVectorMatrix_akivisJacobiator_eq_six_smul_associator]
  module

/-! ## 3. Consequence: Jacobi identity fails -/

/-- The Jacobi identity does not hold for arbitrary split octonions.
    This is the finite algebraic witness that the commutator algebra
    is not a Lie algebra.
-/
theorem jacobi_identity_fails :
    ∃ X Y Z : ZornVectorMatrix ℝ,
      akivisJacobiator X Y Z ≠ 0 := by
  let X : ZornVectorMatrix ℝ := ZornVectorMatrix.U 0
  let Y : ZornVectorMatrix ℝ := ZornVectorMatrix.U 1
  let Z : ZornVectorMatrix ℝ := ZornVectorMatrix.U 2
  refine ⟨X, Y, Z, ?_⟩
  intro hzero
  have hassoc : _root_.associator X Y Z = 0 := by
    have hmul := (akivis_identity X Y Z).symm.trans hzero
    exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)
  exact ZornVectorMatrix.associator_U_zero_U_one_U_two_ne_zero hassoc

end InfoGeometry.Lie.SplitOctonionMalcevCorrection
