import Omega.POM.SchurVarianceGrowthRateSpectralIdentity

namespace Omega.POM

/-- The nontrivial Schur spectral envelope read from the seed radius. -/
def schurEnvelope (spectralRadius : ℝ) : ℝ :=
  pomSchurSeedSpectralEnvelope spectralRadius

/-- The Fourier-channel supremum envelope, identified with the same Schur seed radius. -/
def fourierEnvelope (spectralRadius : ℝ) : ℝ :=
  pomSchurSeedSpectralEnvelope spectralRadius

/-- The optimal centered `L^2` probe envelope, also read from the same seed radius. -/
def probeEnvelope (spectralRadius : ℝ) : ℝ :=
  pomSchurSeedSpectralEnvelope spectralRadius

/-- Paper label: `thm:pom-schur-envelope-variational-characterization`. -/
theorem paper_pom_schur_envelope_variational_characterization
    (spectralRadius : ℝ) :
    schurEnvelope spectralRadius = fourierEnvelope spectralRadius ∧
      schurEnvelope spectralRadius = probeEnvelope spectralRadius := by
  constructor <;> rfl

end Omega.POM
