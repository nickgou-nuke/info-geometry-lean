import InfoGeometry.Algebra.H3ZornMcCrimmonLinearization

/-!
# Quadratic representation of the real split Albert algebra

This module derives the denominator-free identity
`4 U_X = 2 P_X² - P_{P_X X}`, with `P_X(Z) = T(X,1,Z)`, from
McCrimmon's identity (12).  The proof is structural and follows the
quadratic-representation chain.
-/

namespace InfoGeometry.Algebra.H3Zorn

private theorem linearTrace_one_real : linearTrace (1 : H3Zorn ℝ) = 3 := by
  change (1 : ℝ) + 1 + 1 = 3
  norm_num

private theorem traceBilin_one_left (X : H3Zorn ℝ) :
    traceBilin 1 X = linearTrace X := by
  rw [traceBilin_symm, traceBilin_one]

private theorem crossProduct_one_left (X : H3Zorn ℝ) :
    crossProduct 1 X = linearTrace X • (1 : H3Zorn ℝ) - X := by
  rw [crossProduct_symm, crossProduct_one]

private theorem linearTrace_neg (X : H3Zorn ℝ) :
    linearTrace (-X) = -linearTrace X := by
  rw [show -X = (-1 : ℝ) • X by module, linearTrace_smul]
  ring

private theorem linearTrace_sub (X Y : H3Zorn ℝ) :
    linearTrace (X - Y) = linearTrace X - linearTrace Y := by
  simp only [sub_eq_add_neg, linearTrace_add, linearTrace_neg]

private theorem traceBilin_neg_left (X Y : H3Zorn ℝ) :
    traceBilin (-X) Y = -traceBilin X Y := by
  rw [show -X = (-1 : ℝ) • X by module, traceBilin_smul_left]
  ring

private theorem crossProduct_neg_left (X Y : H3Zorn ℝ) :
    crossProduct (-X) Y = -crossProduct X Y := by
  rw [show -X = (-1 : ℝ) • X by module, crossProduct_smul_left]
  module

private theorem crossProduct_neg_right (X Y : H3Zorn ℝ) :
    crossProduct X (-Y) = -crossProduct X Y := by
  rw [crossProduct_symm, crossProduct_neg_left, crossProduct_symm X Y]

private theorem T_one_formula (X Z : H3Zorn ℝ) :
    T X 1 Z = linearTrace X • Z + linearTrace Z • X + crossProduct X Z -
      linearTrace (crossProduct X Z) • (1 : H3Zorn ℝ) := by
  rw [T_outer_formula, traceBilin_one, traceBilin_one, crossProduct_one]
  module

/-- Specializing McCrimmon's identity (12) at the cubic basepoint solves for
an iterated cross product needed by the quadratic representation formula. -/
private theorem key_X_cross_XcrossZ (X Z : H3Zorn ℝ) :
    crossProduct X (crossProduct X Z) =
      (linearTrace Z •
            (linearTrace (adjointQuad X) • (1 : H3Zorn ℝ) - adjointQuad X) -
          crossProduct (adjointQuad X) Z +
        (linearTrace X •
          (linearTrace (crossProduct X Z) • (1 : H3Zorn ℝ) -
            crossProduct X Z))) -
      (linearTrace (adjointQuad X) • Z +
        traceBilin (adjointQuad X) Z • (1 : H3Zorn ℝ) +
        linearTrace (crossProduct X Z) • X) := by
  have h := mccrimmon_identity_12 X 1 Z
  simp only [crossProduct_one_left, crossProduct_one,
    crossProduct_add_left, crossProduct_add_right,
    crossProduct_smul_left, crossProduct_smul_right,
    crossProduct_neg_left, crossProduct_neg_right, sub_eq_add_neg,
    traceBilin_one, traceBilin_one_left,
    traceBilin_add_left, traceBilin_smul_left, traceBilin_neg_left] at h
  let L0 : H3Zorn ℝ :=
    linearTrace Z •
          (linearTrace (adjointQuad X) • (1 : H3Zorn ℝ) - adjointQuad X) -
      crossProduct (adjointQuad X) Z +
      linearTrace X •
        (linearTrace (crossProduct X Z) • (1 : H3Zorn ℝ) -
          crossProduct X Z)
  let R0 : H3Zorn ℝ :=
    linearTrace (adjointQuad X) • Z +
      traceBilin (adjointQuad X) Z • (1 : H3Zorn ℝ) +
      linearTrace (crossProduct X Z) • X
  change crossProduct X (crossProduct X Z) = L0 - R0
  have h' : L0 - crossProduct X (crossProduct X Z) = R0 := by
    dsimp [L0, R0]
    rw [linearTrace_crossProduct] at h ⊢
    rw [traceBilin_symm Z X] at h
    convert h using 1 <;> module
  calc
    crossProduct X (crossProduct X Z) =
        L0 - (L0 - crossProduct X (crossProduct X Z)) := by
      abel
    _ = L0 - R0 := by rw [h']

/-- Denominator-free quadratic-representation formula
`4 U_X = 2 P_X² - P_{P_X X}`, where `P_X(Z) = T(X,1,Z)`.
It follows structurally from McCrimmon's identity (12). -/
theorem four_U (X Z : H3Zorn ℝ) :
    (4 : ℝ) • U X Z =
      (2 : ℝ) • T X 1 (T X 1 Z) - T (T X 1 X) 1 Z := by
  simp only [T_one_formula]
  simp only [U, crossProduct_self, sub_eq_add_neg,
    linearTrace_add,
    linearTrace_smul, linearTrace_neg, linearTrace_crossProduct,
    crossProduct_add_left, crossProduct_add_right,
    crossProduct_smul_left, crossProduct_smul_right,
    crossProduct_neg_left, crossProduct_neg_right,
    crossProduct_one, crossProduct_one_left, linearTrace_one_real]
  rw [key_X_cross_XcrossZ, linearTrace_crossProduct,
    ← traceBilin_crossProduct_assoc X X Z, crossProduct_self,
    traceBilin_smul_left]
  module

end InfoGeometry.Algebra.H3Zorn
