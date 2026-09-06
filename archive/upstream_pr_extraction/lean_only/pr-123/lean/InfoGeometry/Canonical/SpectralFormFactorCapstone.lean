import InfoGeometry.Spectral.SpectralFormFactor

namespace InfoGeometry.Canonical.SpectralFormFactorCapstone

open InfoGeometry.Spectral.SpectralFormFactor

theorem capstone_spectral_form_factor_synthesis (τ : ℝ) (h_nonneg : 0 ≤ τ) (h_lt : τ < 1) :
    (spectralFormFactor 0 = 0) ∧
    (spectralFormFactor (-τ) = spectralFormFactor τ) ∧
    (spectralFormFactor τ = τ) :=
  grand_spectral_form_factor_synthesis τ h_nonneg h_lt

end InfoGeometry.Canonical.SpectralFormFactorCapstone
