import InfoGeometry.Algebra.H3ZornQuadraticRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornMcCrimmonDualIdentity

/-!
# Cubic multiplication and quadratic representation commutation

This module proves that `P_X = T(X,1,-)` commutes with `U_X`.  The proof is
structural and uses McCrimmon identities (10) and (19), without coordinate
enumeration or cancellation of the cubic norm.
-/

namespace InfoGeometry.Algebra.H3Zorn

private theorem tr_neg (X : H3Zorn ℝ) :
    linearTrace (-X) = -linearTrace X := by
  rw [show -X = (-1 : ℝ) • X by module, linearTrace_smul]
  ring

private theorem tr_sub (X Y : H3Zorn ℝ) :
    linearTrace (X - Y) = linearTrace X - linearTrace Y := by
  simp only [sub_eq_add_neg, linearTrace_add, tr_neg]

private theorem cross_neg_left (X Y : H3Zorn ℝ) :
    crossProduct (-X) Y = -crossProduct X Y := by
  rw [show -X = (-1 : ℝ) • X by module, crossProduct_smul_left]
  module

private theorem cross_neg_right (X Y : H3Zorn ℝ) :
    crossProduct X (-Y) = -crossProduct X Y := by
  rw [crossProduct_symm, cross_neg_left, crossProduct_symm X Y]

private theorem bilin_neg_left (X Y : H3Zorn ℝ) :
    traceBilin (-X) Y = -traceBilin X Y := by
  rw [show -X = (-1 : ℝ) • X by module, traceBilin_smul_left]
  ring

private theorem bilin_neg_right (X Y : H3Zorn ℝ) :
    traceBilin X (-Y) = -traceBilin X Y := by
  rw [traceBilin_symm, bilin_neg_left, traceBilin_symm X Y]

private theorem bilin_one_left (X : H3Zorn ℝ) :
    traceBilin 1 X = linearTrace X := by
  rw [traceBilin_symm, traceBilin_one]

private theorem tone (X Z : H3Zorn ℝ) :
    T X 1 Z =
      linearTrace X • Z + linearTrace Z • X + crossProduct X Z -
        linearTrace (crossProduct X Z) • (1 : H3Zorn ℝ) := by
  rw [T_outer_formula, traceBilin_one, traceBilin_one, crossProduct_one]
  module

/-- Identity (18) in the form needed for multiplication-operator
commutation, derived from McCrimmon identity (10) at the basepoint. -/
private theorem cross_adj_X (X : H3Zorn ℝ) :
    crossProduct (adjointQuad X) X =
      (linearTrace (adjointQuad X) * linearTrace X - normCubic X) •
          (1 : H3Zorn ℝ) -
        linearTrace (adjointQuad X) • X -
        linearTrace X • adjointQuad X := by
  have h := mccrimmon_identity_10 X (1 : H3Zorn ℝ)
  rw [crossProduct_one] at h
  rw [show linearTrace X • (1 : H3Zorn ℝ) - X =
      linearTrace X • (1 : H3Zorn ℝ) + (-1 : ℝ) • X by module] at h
  rw [crossProduct_add_right, crossProduct_smul_right,
    crossProduct_smul_right, crossProduct_one, traceBilin_one] at h
  have hs := congrArg
    (fun W : H3Zorn ℝ =>
      linearTrace X •
          (linearTrace (adjointQuad X) • (1 : H3Zorn ℝ) - adjointQuad X) -
        W)
    h
  convert hs using 1 <;> module

private theorem bilin_self (X : H3Zorn ℝ) :
    traceBilin X X =
      linearTrace X * linearTrace X -
        2 * linearTrace (adjointQuad X) := by
  have h := linearTrace_crossProduct X X
  rw [crossProduct_self, linearTrace_smul] at h
  linarith

private theorem bilin_X_cross_XZ (X Z : H3Zorn ℝ) :
    traceBilin X (crossProduct X Z) =
      2 * traceBilin (adjointQuad X) Z := by
  rw [← traceBilin_crossProduct_assoc X X Z, crossProduct_self,
    traceBilin_smul_left]

private theorem bilin_X_cross_adjZ (X Z : H3Zorn ℝ) :
    traceBilin X (crossProduct (adjointQuad X) Z) =
      (linearTrace (adjointQuad X) * linearTrace X - normCubic X) *
          linearTrace Z -
        linearTrace (adjointQuad X) * traceBilin X Z -
        linearTrace X * traceBilin (adjointQuad X) Z := by
  rw [← traceBilin_crossProduct_assoc X (adjointQuad X) Z,
    crossProduct_symm X (adjointQuad X), cross_adj_X]
  simp only [sub_eq_add_neg, traceBilin_add_left, traceBilin_smul_left,
    bilin_neg_left, bilin_one_left]

/-- The cubic multiplication operator `P_X = T(X,1,-)` commutes with the
quadratic representation `U_X`. -/
theorem P_comm_U (X Z : H3Zorn ℝ) :
    T X 1 (U X Z) = U X (T X 1 Z) := by
  simp only [tone, U, tr_sub, linearTrace_smul, linearTrace_crossProduct]
  simp only [sub_eq_add_neg, traceBilin_add_right, traceBilin_smul_right,
    crossProduct_add_right, crossProduct_smul_right, cross_neg_right]
  rw [mccrimmon_identity_19 X Z]
  rw [mccrimmon_identity_10 X Z]
  rw [cross_adj_X]
  rw [crossProduct_one]
  simp only [traceBilin_smul_right, bilin_neg_right, crossProduct_self]
  rw [bilin_self, bilin_X_cross_XZ, bilin_X_cross_adjZ, traceBilin_one]
  module

end InfoGeometry.Algebra.H3Zorn
