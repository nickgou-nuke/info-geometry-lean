import InfoGeometry.Canonical.SpinorialCore.Algebra

/-!
# Intensity versus derivative-dependent current

The phase-conjugation theorem requires transformation of both the value and
its spatial derivative. Boundary intensity alone is not a flux theorem.
-/

noncomputable section
namespace InfoGeometry.Canonical.SpinorialCore

/-- Current density with its overall real physical coefficient suppressed. -/
def currentDensity (z dz : ℂ) : ℝ := (star z * dz).im

/-- Constant unit phase conjugation reverses the specified current. -/
theorem phase_conjugate_current (phase z dz : ℂ)
    (hphase : star phase * phase = 1) :
    currentDensity (phase * star z) (phase * star dz) = -currentDensity z dz := by
  have h : star (phase * star z) * (phase * star dz) = star (star z * dz) := by
    simp only [star_mul, star_star]
    calc
      z * star phase * (phase * star dz) =
          (star phase * phase) * (z * star dz) := by ring
      _ = star dz * z := by rw [hphase]; ring
  unfold currentDensity
  rw [h]
  simp [add_comm]

/-- Equal intensities can carry different currents. -/
theorem equal_intensity_does_not_determine_current :
    ∃ z₁ dz₁ z₂ dz₂ : ℂ,
      Complex.normSq z₁ = Complex.normSq z₂ ∧
        currentDensity z₁ dz₁ ≠ currentDensity z₂ dz₂ := by
  refine ⟨1, Complex.I, 1, -Complex.I, rfl, ?_⟩
  norm_num [currentDensity]

end InfoGeometry.Canonical.SpinorialCore
