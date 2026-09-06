import Mathlib.Tactic

/-!
# Souriau beta Gaussian finite matrix

Repaired external file: a concrete `2×2` beta-vector matrix and its determinant
as a Lorentzian quadratic form.
-/

noncomputable section

namespace SouriauGaussian

open Matrix

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Symmetric beta-vector matrix for one boost direction. -/
def betaMatrix (b0 bx : ℂ) : Mat2C := !![b0, bx; bx, b0]

/-- The beta-matrix determinant is `b0²-bx²`. -/
theorem beta_matrix_det (b0 bx : ℂ) :
    (betaMatrix b0 bx).det = b0 ^ 2 - bx ^ 2 := by
  simp [betaMatrix, Matrix.det_fin_two]
  ring

/-- The zero determinant locus is the one-dimensional light cone. -/
theorem beta_matrix_null_iff (b0 bx : ℂ) :
    (betaMatrix b0 bx).det = 0 ↔ b0 = bx ∨ b0 = -bx := by
  rw [beta_matrix_det]
  rw [show b0 ^ 2 - bx ^ 2 = (b0 - bx) * (b0 + bx) by ring]
  rw [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

#check beta_matrix_det
#check beta_matrix_null_iff

end SouriauGaussian
