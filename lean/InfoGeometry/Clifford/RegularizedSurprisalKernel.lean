import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.RegularizedSurprisalKernel

noncomputable section

abbrev SpinorMatrix32 := InfoGeometry.Algebra.FiniteSpin.Mat32R

def secondOrder (K : SpinorMatrix32) (β : ℝ) : SpinorMatrix32 :=
  ((1 / 2 : ℝ) * β ^ 2) • (K * K)

theorem secondOrder_trace (K : SpinorMatrix32) (β : ℝ) :
    Matrix.trace (secondOrder K β) =
      ((1 / 2 : ℝ) * β ^ 2) * Matrix.trace (K * K) := by
  unfold secondOrder
  rw [Matrix.trace_smul]
  rfl

theorem secondOrder_zero_of_square_zero
    (K : SpinorMatrix32) (β : ℝ) (hK : K * K = 0) :
    secondOrder K β = 0 := by
  unfold secondOrder
  rw [hK, smul_zero]

theorem secondOrder_is_quadratic_residue
    (K : SpinorMatrix32) (β : ℝ) :
    secondOrder K β = ((1 / 2 : ℝ) * β ^ 2) • (K * K) := by
  rfl

theorem secondOrder_trace_zero_of_square_zero
    (K : SpinorMatrix32) (β : ℝ) (hK : K * K = 0) :
    Matrix.trace (secondOrder K β) = 0 := by
  rw [secondOrder_trace, hK, Matrix.trace_zero, mul_zero]

end
end InfoGeometry.Clifford.RegularizedSurprisalKernel
