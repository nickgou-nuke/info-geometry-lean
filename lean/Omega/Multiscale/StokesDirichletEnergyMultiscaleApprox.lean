import Mathlib.Tactic

namespace Omega.Multiscale

/-- Concrete layer energies, discrete approximations, reference energy, and control sequence. -/
structure StokesDirichletEnergyMultiscaleApproxData where
  layerEnergy : ℕ → ℝ
  liftedCubeEnergy : ℕ → ℝ
  discreteApproximation : ℕ → ℝ
  referenceEnergy : ℝ
  lipschitzControl : ℕ → ℝ

/-- Pullback invariance and degree cancellation make the energy layer-independent, while the
discrete approximation obeys its prescribed error bound. -/
theorem paper_app_stokes_dirichlet_energy_multiscale_approx
    (D : StokesDirichletEnergyMultiscaleApproxData)
    (pullbackLocalIsometry : ∀ n, D.layerEnergy n = D.liftedCubeEnergy n)
    (degreeCancellation : ∀ n, D.liftedCubeEnergy n = D.referenceEnergy)
    (riemannSumError :
      ∀ n, |D.discreteApproximation n - D.referenceEnergy| ≤ D.lipschitzControl n) :
    (∀ n, D.layerEnergy n = D.referenceEnergy) ∧
      (∀ n, D.layerEnergy n = D.layerEnergy 0) ∧
        (∀ n, |D.discreteApproximation n - D.layerEnergy n| ≤ D.lipschitzControl n) := by
  have hWellDefined : ∀ n, D.layerEnergy n = D.referenceEnergy := by
    intro n
    exact (pullbackLocalIsometry n).trans (degreeCancellation n)
  have hLayerIndependent : ∀ n, D.layerEnergy n = D.layerEnergy 0 := by
    intro n
    rw [hWellDefined n, hWellDefined 0]
  have hApprox : ∀ n, |D.discreteApproximation n - D.layerEnergy n| ≤ D.lipschitzControl n := by
    intro n
    simpa [hWellDefined n] using riemannSumError n
  exact ⟨hWellDefined, hLayerIndependent, hApprox⟩

end Omega.Multiscale
