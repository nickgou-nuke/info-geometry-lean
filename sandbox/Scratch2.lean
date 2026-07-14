import Mathlib

lemma exp_neg_two_log_eq_inv_sq (n : ℕ) :
    Complex.exp (-2 * Real.log (n + 1 : ℝ)) = (1 / ((n + 1 : ℝ) ^ 2) : ℂ) := by
  have h_arg : (-2 : ℂ) * ↑(Real.log (n + 1 : ℝ)) = ↑((-2 : ℝ) * Real.log (n + 1 : ℝ)) := by push_cast; rfl
  rw [h_arg, ← Complex.ofReal_exp]
  have h_pow : Real.exp ((-2 : ℝ) * Real.log (n + 1 : ℝ)) = (n + 1 : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_def_of_pos]
    positivity
  rw [h_pow]
  have h_pow_int : (n + 1 : ℝ) ^ (-2 : ℝ) = (n + 1 : ℝ) ^ (-2 : ℤ) := by
    exact Real.rpow_intCast (n + 1 : ℝ) (-2)
  rw [h_pow_int]
  have h_zpow : (n + 1 : ℝ) ^ (-2 : ℤ) = 1 / ((n + 1 : ℝ) ^ 2) := by
    rw [zpow_neg, zpow_two, inv_eq_one_div]
  rw [h_zpow]
  push_cast
  rfl

lemma tsum_complex_cast_inv_sq :
    (∑' (n : ℕ), (1 / ((n + 1 : ℝ) ^ 2) : ℂ)) = ↑(∑' (n : ℕ), 1 / ((n + 1 : ℝ) ^ 2)) := by
  have h := @Complex.ofReal_tsum ℕ (fun n => 1 / ((n + 1 : ℝ) ^ 2))
  exact h.symm
