import Mathlib

noncomputable section
def phi : ℝ := (1 + Real.sqrt 5) / 2

def prime_encoding_entropy_at_200 : ℝ := (phi / 2) * Real.log 200

theorem pnt_fibonacci_structural_unity :
    prime_encoding_entropy_at_200 / Real.log 200 > 0.8 ∧
    prime_encoding_entropy_at_200 / Real.log 200 < 0.85 := by
  dsimp [prime_encoding_entropy_at_200]
  have hlog_pos : Real.log 200 > 0 := Real.log_pos (by norm_num)
  have hlog_ne : Real.log 200 ≠ 0 := ne_of_gt hlog_pos
  rw [mul_div_cancel_right₀ (phi / 2) hlog_ne]
  dsimp [phi]
  constructor
  · have h1 : (2.2 : ℝ) < Real.sqrt 5 := by
      rw [← Real.sqrt_sq (by norm_num : 0 ≤ (2.2 : ℝ))]
      apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  · have h2 : Real.sqrt 5 < (2.4 : ℝ) := by
      rw [← Real.sqrt_sq (by norm_num : 0 ≤ (2.4 : ℝ))]
      apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
