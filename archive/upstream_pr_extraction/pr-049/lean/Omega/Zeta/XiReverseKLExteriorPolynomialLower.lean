theorem xi_reversekl_exterior_polynomial_lower
    (fenchelPoissonDuality jensenExteriorWitness fourierCoefficientExpansion explicitLowerBound :
      Prop)
    (hDual : fenchelPoissonDuality)
    (hJensen : jensenExteriorWitness)
    (hFourier : fourierCoefficientExpansion)
    (hLower :
      fenchelPoissonDuality →
        jensenExteriorWitness →
          fourierCoefficientExpansion →
            explicitLowerBound) :
    fenchelPoissonDuality ∧
      jensenExteriorWitness ∧
        fourierCoefficientExpansion ∧
          explicitLowerBound := by
  exact ⟨hDual, hJensen, hFourier, hLower hDual hJensen hFourier⟩

/-- Paper-facing wrapper for the exterior analytic polynomial witness lower bound.
    thm:xi-reversekl-exterior-analytic-witness-log -/
theorem xi_reversekl_exterior_analytic_lower_log
    (fenchelPoissonDuality jensenExteriorWitness finiteFourierCoefficients
      analyticExteriorLowerBound : Prop)
    (hDual : fenchelPoissonDuality)
    (hJensen : jensenExteriorWitness)
    (hFourier : finiteFourierCoefficients)
    (hLower :
      fenchelPoissonDuality →
        jensenExteriorWitness →
          finiteFourierCoefficients →
            analyticExteriorLowerBound) :
    fenchelPoissonDuality ∧
      jensenExteriorWitness ∧
        finiteFourierCoefficients ∧
          analyticExteriorLowerBound := by
  exact ⟨hDual, hJensen, hFourier, hLower hDual hJensen hFourier⟩
