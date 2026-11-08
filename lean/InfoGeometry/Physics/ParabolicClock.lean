import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace InfoGeometry.Physics

variable {R : Type*} [CommRing R]

/-- The nilpotent operator `K` representing the null direction on the Krein boundary. -/
def K : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- The parabolic clock dictates that the operator squares to zero. -/
theorem K_sq_eq_zero : K * K = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K, Matrix.mul_apply, Fin.sum_univ_two]

/-- The null generator is traceless. -/
theorem K_trace_eq_zero : Matrix.trace (K (R := R)) = 0 := by
  simp [K, Matrix.trace, Fin.sum_univ_two]

/-- The null generator has vanishing determinant. -/
theorem K_det_eq_zero : (K (R := R)).det = 0 := by
  simp [K, Matrix.det_fin_two]

/-- Exponentiation of the parabolic flow: exp(tK) = I + tK. -/
def parabolicFlow (t : R) : Matrix (Fin 2) (Fin 2) R :=
  1 + t • K

/-- The parabolic flow preserves the projective scaling freedom (det = 1). -/
theorem parabolic_det_one (t : R) : (parabolicFlow t).det = 1 := by
  dsimp [parabolicFlow, K]
  simp [Matrix.det_fin_two]

/-- The parabolic flow keeps trace `2`, hence is unipotent/parabolic. -/
theorem parabolic_trace_two (t : R) : Matrix.trace (parabolicFlow t) = 2 := by
  simp [parabolicFlow, K, Matrix.trace_fin_two]

/-- Subtracting the identity from the parabolic flow recovers a square-zero step. -/
theorem parabolicFlow_sub_one_sq_eq_zero (t : R) :
    (parabolicFlow t - 1) * (parabolicFlow t - 1) = (0 : Matrix (Fin 2) (Fin 2) R) := by
  have hscaled : (t • K : Matrix (Fin 2) (Fin 2) R) * (t • K) = 0 := by
    calc
      (t • K : Matrix (Fin 2) (Fin 2) R) * (t • K)
          = (t * t) • (K * K) := by simp [mul_smul]
      _ = 0 := by simp [K_sq_eq_zero]
  simpa [parabolicFlow, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaled

/-- The parabolic flow is explicitly classified by determinant `1` and trace `2`. -/
theorem parabolic_classification (t : R) :
    (parabolicFlow t).det = 1 ∧ Matrix.trace (parabolicFlow t) = 2 := by
  exact ⟨parabolic_det_one t, parabolic_trace_two t⟩

end InfoGeometry.Physics
