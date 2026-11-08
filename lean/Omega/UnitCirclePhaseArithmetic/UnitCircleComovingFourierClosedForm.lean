import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed

namespace Omega.UnitCirclePhaseArithmetic

/-- Unit-circle wrapper for the typed-address comoving Fourier closed-form package.
    prop:unit-circle-comoving-fourier-closed-form -/
theorem paper_unit_circle_comoving_fourier_closed_form
    (D : Omega.TypedAddressBiaxialCompletion.ComovingFourierClosedData)
    (hLorentzProfileModel : D.lorentzProfileModel)
    (hExplicitFourierFormulaInput : D.explicitFourierFormulaInput)
    (hPositiveFrequencyRestriction : D.positiveFrequencyRestriction)
    (hIntervalUniquenessPrinciple : D.intervalUniquenessPrinciple) :
    D.fourierClosedForm ∧ D.finiteExponentialSpectrum ∧ D.openIntervalInjective := by
  exact
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_fourier_closed
      D
      hLorentzProfileModel
      hExplicitFourierFormulaInput
      hPositiveFrequencyRestriction
      hIntervalUniquenessPrinciple

end Omega.UnitCirclePhaseArithmetic
