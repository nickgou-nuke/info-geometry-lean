import Mathlib

open Real

lemma test_rpow (p : ℝ) (hp : 1 < p) (y : ℝ) (h : p ^ y = 1) : y = 0 := by
  have hpos : 0 < p := by positivity
  have hlog : Real.log (p ^ y) = Real.log 1 := by rw [h]
  rw [Real.log_rpow hpos, Real.log_one] at hlog
  have hlogp : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hp)
  cases mul_eq_zero.mp hlog with
  | inl hy => exact hy
  | inr hp0 => exact False.elim (hlogp hp0)
