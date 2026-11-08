import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InfoGeometry.Canonical.FibonacciPartition

noncomputable def UpperPhi : ℝ := (1 + Real.sqrt 5) / 2
noncomputable def LowerPhi : ℝ := (Real.sqrt 5 - 1) / 2

theorem UpperPhi_eq_one_add_LowerPhi : UpperPhi = 1 + LowerPhi := by
  unfold UpperPhi LowerPhi
  ring

theorem UpperPhi_sq : UpperPhi ^ 2 = UpperPhi + 1 := by
  unfold UpperPhi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by linarith)
  ring_nf
  rw [h5]
  ring

theorem Fibonacci_scale_decomp : 20 * UpperPhi ^ 4 = 100 + 60 * LowerPhi := by
  have h_sq := UpperPhi_sq
  have h4 : UpperPhi ^ 4 = (UpperPhi ^ 2) ^ 2 := by ring
  rw [h4, h_sq]
  have h_sq2 : (UpperPhi + 1) ^ 2 = UpperPhi ^ 2 + 2 * UpperPhi + 1 := by ring
  rw [h_sq2, h_sq]
  have h_phi : UpperPhi = 1 + LowerPhi := UpperPhi_eq_one_add_LowerPhi
  rw [h_phi]
  ring

-- Statistical Partition Functions: B(x) = 1/(1-x), F(x) = 1+x
noncomputable def bosonicFactor (x : ℝ) : ℝ := 1 / (1 - x)
def fermionicFactor (x : ℝ) : ℝ := 1 + x

/-- The exact supersymmetry difference identity: B(x) - F(x) = x^2 * B(x). -/
theorem bosonic_minus_fermionic_eq_sq_mul_bosonic (x : ℝ) (h : x ≠ 1) :
    bosonicFactor x - fermionicFactor x = x ^ 2 * bosonicFactor x := by
  unfold bosonicFactor fermionicFactor
  have h_diff : 1 - x ≠ 0 := by
    intro hc
    have : x = 1 := by linarith
    exact h this
  field_simp [h_diff]
  ring

end InfoGeometry.Canonical.FibonacciPartition
