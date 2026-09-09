import InfoGeometry.Spectral.SpectralFormFactor

namespace InfoGeometry.Canonical.SpectralFormFactorCapstone

open InfoGeometry.Spectral.SpectralFormFactor

/-- Canonical packaging of the elementary spectral-form-factor identities. -/
theorem capstone_spectral_form_factor_synthesis (τ : ℝ) (h_nonneg : 0 ≤ τ) (h_lt : τ < 1) :
    (spectralFormFactor 0 = 0) ∧
    (spectralFormFactor (-τ) = spectralFormFactor τ) ∧
    (spectralFormFactor τ = τ) := by
  exact ⟨sff_at_zero, sff_even τ, sff_ramp τ h_nonneg h_lt⟩

end InfoGeometry.Canonical.SpectralFormFactorCapstone
