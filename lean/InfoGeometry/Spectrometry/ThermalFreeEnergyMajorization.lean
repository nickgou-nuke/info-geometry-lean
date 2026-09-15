import InfoGeometry.Spectrometry.DecoupledThermodynamicsFluctuations

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

noncomputable section

theorem lineFreeEnergy_le_tangent (anchor candidate cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) :
    lineFreeEnergy candidate cutoff temperature ≤
      lineFreeEnergy anchor cutoff temperature +
        lineWeight anchor cutoff temperature * (candidate - anchor) := by
  have concave := (strictConcaveOn_lineFreeEnergy cutoff temperature temperature_pos).concaveOn
  have derivative := hasDerivAt_lineFreeEnergy anchor cutoff temperature temperature_pos
  rcases lt_trichotomy anchor candidate with forward | equal | backward
  · have bound := concave.slope_le_of_hasDerivAt (Set.mem_univ anchor)
      (Set.mem_univ candidate) forward derivative
    rw [slope_def_field] at bound
    have scaled := (div_le_iff₀ (sub_pos.mpr forward)).mp bound
    linarith
  · subst candidate
    simp
  · have bound := concave.le_slope_of_hasDerivAt (Set.mem_univ candidate)
      (Set.mem_univ anchor) backward derivative
    rw [slope_def_field] at bound
    have scaled := (le_div_iff₀ (sub_pos.mpr backward)).mp bound
    nlinarith

theorem lineFreeEnergy_le_quadratic (anchor candidate cutoff temperature : ℝ)
    (anchor_pos : 0 < anchor) (temperature_pos : 0 < temperature) :
    lineFreeEnergy candidate cutoff temperature ≤
      lineFreeEnergy anchor cutoff temperature +
        (lineWeight anchor cutoff temperature / anchor / 2) *
          (candidate ^ 2 - anchor ^ 2) := by
  have spatial : candidate - anchor ≤ (candidate ^ 2 - anchor ^ 2) / (2 * anchor) := by
    apply (le_div_iff₀ (mul_pos two_pos anchor_pos)).mpr
    nlinarith [sq_nonneg (candidate - anchor)]
  have weighted := mul_le_mul_of_nonneg_left spatial
    (line_weight_bounds anchor cutoff temperature).1.le
  calc
    _ ≤ lineFreeEnergy anchor cutoff temperature +
        lineWeight anchor cutoff temperature * (candidate - anchor) :=
      lineFreeEnergy_le_tangent anchor candidate cutoff temperature temperature_pos
    _ ≤ lineFreeEnergy anchor cutoff temperature +
        lineWeight anchor cutoff temperature *
          ((candidate ^ 2 - anchor ^ 2) / (2 * anchor)) := add_le_add_left weighted _
    _ = _ := by ring

end

end InfoGeometry.Spectrometry.DecoupledThermodynamics
