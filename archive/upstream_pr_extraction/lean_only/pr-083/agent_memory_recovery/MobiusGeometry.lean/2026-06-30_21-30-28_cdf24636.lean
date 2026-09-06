  rw [one_mul] at h1
  exact h1

theorem hyperbolic_trace_bound (L : ℝ) (h : L ≠ 0) : (L + L⁻¹)^2 - 4 = (L - L⁻¹)^2 := by
  ring

def matrix_sq_trace (L : ℂ) : ℂ := (L^2 + (L⁻¹)^2)^2
