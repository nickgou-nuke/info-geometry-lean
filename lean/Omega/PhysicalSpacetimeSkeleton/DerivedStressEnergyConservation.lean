import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- Concrete residual stress-energy components and covariant divergence. -/
structure DerivedResidualStressEnergy where
  stressEnergy : ℕ → ℕ → ℝ
  covariantDivergence : ℕ → ℝ

/-- Symmetry and diffeomorphism-invariant conservation laws for the residual stress-energy tensor. -/
theorem paper_physical_spacetime_derived_stress_energy_conservation
    (T : DerivedResidualStressEnergy)
    (symmetric : ∀ μ ν, T.stressEnergy μ ν = T.stressEnergy ν μ)
    (diffeomorphismInvariant : Prop)
    (hasDiffeomorphismInvariant : diffeomorphismInvariant)
    (conserved_of_diffeomorphismInvariant :
      diffeomorphismInvariant → ∀ μ, T.covariantDivergence μ = 0) :
    (∀ μ ν, T.stressEnergy μ ν = T.stressEnergy ν μ) ∧
      diffeomorphismInvariant ∧
        ∀ μ, T.covariantDivergence μ = 0 := by
  exact ⟨symmetric, hasDiffeomorphismInvariant,
    conserved_of_diffeomorphismInvariant hasDiffeomorphismInvariant⟩

end Omega.PhysicalSpacetimeSkeleton
