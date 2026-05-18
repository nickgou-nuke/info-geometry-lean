import Mathlib

open Real

def isBarrierKernel (x : ℝ) : ℝ := x - Real.log x - 1
def isBarrierKernel_deriv2 (x : ℝ) : ℝ := 1 / x ^ 2
def isBarrierKernel_deriv3 (x : ℝ) : ℝ := -2 / x ^ 3

theorem isBarrierKernel_selfConcordance (x : ℝ) (hx : 0 < x) :
    |isBarrierKernel_deriv3 x| = 2 * isBarrierKernel_deriv2 x ^ (3 / 2 : ℝ) := by
  unfold isBarrierKernel_deriv3 isBarrierKernel_deriv2
  have hinv : 0 < x⁻¹ := inv_pos.mpr hx
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  rw [abs_of_nonpos (by positivity : -2 / x ^ 3 ≤ 0)]
  rw [show -((-2) / x ^ 3) = 2 * x⁻¹ ^ 3 by rw [inv_pow]; ring]
  rw [show (1 : ℝ) / x ^ 2 = x⁻¹ ^ 2 by rw [inv_pow]; ring]
  have h2 : (x⁻¹ ^ 2 : ℝ) = x⁻¹ ^ (2 : ℝ) := by norm_cast
  rw [h2, ← Real.rpow_mul (le_of_lt hinv)]
  norm_num

theorem singlePrimeBarrier_pos_off_criticalLine_test
    (p : ℕ) (hp : 1 < p) (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    0 < isBarrierKernel ((p : ℝ) ^ (2 * ((1 : ℝ) / 2 - σ))) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hpow_pos : 0 < (p : ℝ) ^ (2 * (1 / 2 - σ)) := Real.rpow_pos_of_pos hpos _
  have hne : (p : ℝ) ^ (2 * (1 / 2 - σ)) ≠ 1 := by
    intro h
    have hlog : Real.log ((p : ℝ) ^ (2 * (1 / 2 - σ))) = Real.log 1 := by rw [h]
    rw [Real.log_rpow hpos, Real.log_one] at hlog
    have hlogp : Real.log p ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
    cases mul_eq_zero.mp hlog with
    | inl hy => linarith
    | inr hp0 => exact False.elim (hlogp hp0)
  -- wait, I don't have isBarrierKernel_pos here, but I just wanted to test the hne part.
  sorry

