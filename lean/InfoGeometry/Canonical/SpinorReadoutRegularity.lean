import InfoGeometry.Canonical.SpinorHydrodynamicReadout

/-!
# Quantitative regularity of the spinorial quotient

The coefficient three follows from the differentiated current and density.
The estimates use actual derivatives along curves and the native spatial
Fréchet derivative. Positive density and spatial derivative control remain
explicit hypotheses; bounded state norm alone is not substituted for them.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinorHydrodynamicReadout

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem abs_densityRate_le (z dz : E) :
    |densityRate z dz| ≤ 2 * ‖z‖ * ‖dz‖ := by
  rw [densityRate, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (mul_le_mul_of_nonneg_left (abs_inner_re_le z dz) (by norm_num)).trans_eq
    (mul_assoc _ _ _).symm

theorem abs_currentRate_le {kappa : ℝ} (hk : 0 ≤ kappa) (z dz v dv : E) :
    |currentRate kappa z dz v dv| ≤ kappa * (‖z‖ * ‖dv‖ + ‖dz‖ * ‖v‖) := by
  rw [currentRate, abs_mul, abs_of_nonneg hk]
  apply mul_le_mul_of_nonneg_left _ hk
  exact (abs_add_le _ _).trans (add_le_add (abs_inner_im_le z dv) (abs_inner_im_le dz v))

/-- The directional reconstruction bound, with its exact coefficient three. -/
theorem abs_readoutRate_le {kappa : ℝ} (hk : 0 ≤ kappa) {z : E}
    (hz : z ≠ 0) (dz v dv : E) :
    |readoutRate kappa z dz v dv| ≤
      kappa * (‖dv‖ / ‖z‖ + 3 * ‖dz‖ * ‖v‖ / ‖z‖ ^ 2) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hr : 0 < density z := (density_pos_iff z).mpr hz
  rw [readoutRate, abs_div, abs_of_nonneg (sq_nonneg (density z))]
  calc
    |currentRate kappa z dz v dv * density z - current kappa z v * densityRate z dz| /
        density z ^ 2 ≤
        (|currentRate kappa z dz v dv| * density z +
          |current kappa z v| * |densityRate z dz|) / density z ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [abs_mul, abs_of_pos hr] using
        abs_sub (currentRate kappa z dz v dv * density z)
          (current kappa z v * densityRate z dz)
    _ ≤ (kappa * (‖z‖ * ‖dv‖ + ‖dz‖ * ‖v‖) * density z +
          (kappa * ‖z‖ * ‖v‖) * (2 * ‖z‖ * ‖dz‖)) / density z ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (abs_currentRate_le hk z dz v dv) hr.le
      · exact mul_le_mul (abs_current_le hk z v) (abs_densityRate_le z dz)
          (abs_nonneg _) (by positivity)
    _ = kappa * (‖dv‖ / ‖z‖ + 3 * ‖dz‖ * ‖v‖ / ‖z‖ ^ 2) := by
      dsimp [density]
      field_simp
      ring

/-- The bound applies to the actual scalar derivative, not only a formal jet. -/
theorem abs_deriv_readout_le {kappa : ℝ} (hk : 0 ≤ kappa)
    {f g : ℝ → E} {df dg : E} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) (hz : f t ≠ 0) :
    |deriv (fun r => readout kappa (f r) (g r)) t| ≤
      kappa * (‖dg‖ / ‖f t‖ + 3 * ‖df‖ * ‖g t‖ / ‖f t‖ ^ 2) := by
  rw [(hasDerivAt_readout kappa hf hg hz).deriv]
  exact abs_readoutRate_le hk hz df (g t) dg

section Spatial

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The spatial velocity covector evaluated on a direction, using native fderiv. -/
def spatialReadout (kappa : ℝ) (psi : X → E) (x direction : X) : ℝ :=
  readout kappa (psi x) (fderiv ℝ psi x direction)

theorem spatialReadout_eq_of_hasFDerivAt (kappa : ℝ) {psi : X → E} {x : X}
    {D : X →L[ℝ] E} (hD : HasFDerivAt psi D x) (direction : X) :
    spatialReadout kappa psi x direction = readout kappa (psi x) (D direction) := by
  simp only [spatialReadout, hD.fderiv]

/-- Fréchet operator norm controls every spatial component away from nodes. -/
theorem abs_spatialReadout_le {kappa : ℝ} (hk : 0 ≤ kappa)
    (psi : X → E) {x : X} (hz : psi x ≠ 0) (direction : X) :
    |spatialReadout kappa psi x direction| ≤
      kappa * ‖fderiv ℝ psi x‖ * ‖direction‖ / ‖psi x‖ := by
  apply (abs_readout_le hk hz (fderiv ℝ psi x direction)).trans
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left ((fderiv ℝ psi x).le_opNorm direction) hk).trans_eq
    (mul_assoc _ _ _).symm

end Spatial

end InfoGeometry.Canonical.SpinorHydrodynamicReadout
