import proofs.HIndexFin10Reindex

/-! # Rational diagonalization of the hyperbolic `(5,5)` metric -/

noncomputable section
set_option maxHeartbeats 800000
namespace SO55RationalDiagonalization

open SplitOctonionTKK55
open HIndexFin10Reindex

def basisChange : M10 :=
  1 + Matrix.single 0 9 1 + Matrix.single 9 0 (1 / 2 : ℝ) +
    Matrix.single 9 9 (-3 / 2 : ℝ)

def basisChangeInv : M10 :=
  1 + Matrix.single 0 0 (-1 / 2 : ℝ) + Matrix.single 0 9 1 +
    Matrix.single 9 0 (1 / 2 : ℝ) + Matrix.single 9 9 (-2 : ℝ)

theorem singleProduct (i j k l : Fin 10) (a b : ℝ) :
    Matrix.single i j a * Matrix.single k l b =
      if j = k then Matrix.single i l (a * b) else 0 := by
  by_cases h : j = k
  · subst k
    rw [Matrix.single_mul_single_same]
    simp
  · rw [Matrix.single_mul_single_of_ne a i j k h b]
    simp [h]

theorem basisChangeInv_mul : basisChangeInv * basisChange = 1 := by
  simp only [basisChangeInv, basisChange, add_mul, mul_add, one_mul, mul_one,
    singleProduct]
  ext i j
  by_cases hi0 : i = 0 <;> by_cases hi9 : i = 9 <;>
    by_cases hj0 : j = 0 <;> by_cases hj9 : j = 9 <;>
    simp [Matrix.single, Matrix.one_apply, hi0, hi9, hj0, hj9, eq_comm] <;> ring

theorem basisChange_mul_inv : basisChange * basisChangeInv = 1 := by
  simp only [basisChangeInv, basisChange, add_mul, mul_add, one_mul, mul_one,
    singleProduct]
  ext i j
  by_cases hi0 : i = 0 <;> by_cases hi9 : i = 9 <;>
    by_cases hj0 : j = 0 <;> by_cases hj9 : j = 9 <;>
    simp [Matrix.single, Matrix.one_apply, hi0, hi9, hj0, hj9, eq_comm] <;> ring

def hyperbolicMetricSparse : M10 :=
  eta55 - Matrix.single 0 0 1 + Matrix.single 9 9 1 +
    Matrix.single 0 9 1 + Matrix.single 9 0 1

end SO55RationalDiagonalization
end noncomputable section
