import Mathlib
open Real

lemma isBarrierKernel_not_inv_eq :
  (2 : ℝ) - Real.log 2 - 1 ≠ (1 / 2 : ℝ) - Real.log (1 / 2) - 1 := by
  intro h
  have h1 : Real.log (1 / 2) = - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [h1] at h
  have h2 : (2 : ℝ) - 1 = 1 := by norm_num
  have h3 : (1 / 2 : ℝ) - 1 = - 1 / 2 := by norm_num
  linarith
