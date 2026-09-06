  intro R_x
  change (x - 2 * ((x * a - r) / (a * a)) * a) - 2 * (((x - 2 * ((x * a - r) / (a * a)) * a) * a - r) / (a * a)) * a = x
  have ha2 : a * a ≠ 0 := mul_ne_zero h h
  field_simp
  ring


theorem minkowski_det (x0 x1 x2 x3 : ℝ) :
  (x0 + x1 : ℂ) * (x0 - x1 : ℂ) - (x2 + x3 * I) * (x2 - x3 * I) = (x0^2 - x1^2 - x2^2 - x3^2 : ℝ) := by
  ext <;> simp <;> ring

end InfoGeometry
