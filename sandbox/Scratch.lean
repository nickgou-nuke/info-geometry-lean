import Mathlib
import Mathlib.NumberTheory.ZetaValues

open Real

lemma sum_shift : (∑' (n : ℕ), 1 / ((n + 1 : ℝ) ^ 2)) = Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two.tsum_eq
  have h2 : (∑' (n : ℕ), 1 / (n : ℝ) ^ 2) = (1 / (0 : ℝ) ^ 2) + ∑' (n : ℕ), 1 / ((n + 1 : ℝ) ^ 2) := by
    apply tsum_eq_zero_add
    exact hasSum_zeta_two.summable
  rw [h] at h2
  have h3 : (1 : ℝ) / (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h3, zero_add] at h2
  exact h2.symm
