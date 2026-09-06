def matrix_sq_trace (L : ℂ) : ℂ := (L^2 + (L⁻¹)^2)^2

theorem iter_trace_bound (L : ℂ) (h : L ≠ 0) : matrix_sq_trace L = ( (L + L⁻¹)^2 - 2 )^2 := by
  dsimp [matrix_sq_trace]
  have h1 : L * L⁻¹ = 1 := mul_inv_cancel₀ h
  congr 1
  calc L^2 + (L⁻¹)^2
    _ = (L + L⁻¹)^2 - 2 * (L * L⁻¹) := by ring
    _ = (L + L⁻¹)^2 - 2 * 1 := by rw [h1]
    _ = (L + L⁻¹)^2 - 2 := by ring

theorem hyperplane_reflection_involution (x a r : ℝ) (h : a ≠ 0) :
  let R_x := x - 2 * ((x * a - r) / (a * a)) * a;
  R_x - 2 * ((R_x * a - r) / (a * a)) * a = x := by
  intro R_x
    _ = x - 2 * ((x * a - r) / (a * a)) * a - 2 * (((x * a - 2 * (x * a - r) * 1 - r)) / (a * a)) * a := by rw [h2]
    _ = x - 2 * ((x * a - r) / (a * a)) * a - 2 * ((- (x * a - r)) / (a * a)) * a := by ring
    _ = x := by ring

end InfoGeometry
