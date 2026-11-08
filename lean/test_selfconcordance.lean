import Mathlib

open Real

lemma test_selfConcordance (x : ℝ) (hx : 0 < x) :
  2 * x⁻¹ ^ 3 = 2 * (x⁻¹ ^ 2 : ℝ) ^ (3 / 2 : ℝ) := by
  have hinv : 0 < x⁻¹ := inv_pos.mpr hx
  congr 1
  -- need to prove `a ^ 3 = (a ^ 2) ^ (3/2)` for `a > 0`
  have h2 : (x⁻¹ ^ 2 : ℝ) = x⁻¹ ^ (2 : ℝ) := by norm_cast
  rw [h2, ← Real.rpow_mul (le_of_lt hinv)]
  norm_num
