          exact F.rotor_right_inv s
  calc
    y = y * (x * z) := by rw [hxz, ContinuousLinearMap.comp_id]
    _ = (y * x) * z := by rw [mul_assoc]
    _ = z := by rw [hyx, ContinuousLinearMap.id_comp]


/- The rotor conjugation actions compose by adding their parameters. -/
theorem sigma_comp (s t : ℝ) (A : RealEnd E) :
    F.sigma s (F.sigma t A) = F.sigma (s + t) A := by
  ext v