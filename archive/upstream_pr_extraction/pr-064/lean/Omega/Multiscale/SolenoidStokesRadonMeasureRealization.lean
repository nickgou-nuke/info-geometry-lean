import Mathlib.Tactic

namespace Omega.Multiscale

/-- Concrete carriers and maps for realizing a limiting Stokes functional by a Radon measure. -/
structure SolenoidStokesRadonMeasureData where
  Level : Type
  TopDegreeForm : Type
  l1Completion : Type
  finiteLevelMass : Level → ℝ
  inverseLimitCylinderMass : Level → ℝ
  topDegreeIntegral : TopDegreeForm → ℝ
  stokesFunctional : TopDegreeForm → ℝ
  l1Functional : l1Completion → ℝ
  densityLift : TopDegreeForm → l1Completion

/-- The finite-level, Stokes, and `L¹` compatibility laws give the Radon readout identities. -/
theorem paper_app_solenoid_stokes_radon_measure_realization
    (D : SolenoidStokesRadonMeasureData)
    (finiteLevelCompatibility :
      ∀ ℓ, D.inverseLimitCylinderMass ℓ = D.finiteLevelMass ℓ)
    (stokesEqualsIntegral :
      ∀ ω, D.stokesFunctional ω = D.topDegreeIntegral ω)
    (l1ExtensionAgrees :
      ∀ ω, D.l1Functional (D.densityLift ω) = D.stokesFunctional ω) :
    (∀ ℓ, D.inverseLimitCylinderMass ℓ = D.finiteLevelMass ℓ) ∧
      (∀ ω, D.stokesFunctional ω = D.topDegreeIntegral ω) ∧
        (∀ ω, D.l1Functional (D.densityLift ω) = D.topDegreeIntegral ω) := by
  refine ⟨finiteLevelCompatibility, stokesEqualsIntegral, ?_⟩
  intro ω
  exact (l1ExtensionAgrees ω).trans (stokesEqualsIntegral ω)

end Omega.Multiscale
