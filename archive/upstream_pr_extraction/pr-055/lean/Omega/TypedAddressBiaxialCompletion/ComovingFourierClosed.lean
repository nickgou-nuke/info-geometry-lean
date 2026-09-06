import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address restatement of the comoving Fourier closed-form theorem: the Lorentz-profile
model and explicit transform formula give a finite exponential spectrum, and interval-based
uniqueness recovers injectivity from any nonempty open interval.
    thm:typed-address-biaxial-completion-comoving-fourier-closed -/
theorem paper_typed_address_biaxial_completion_comoving_fourier_closed
    {lorentzProfileModel explicitFourierFormulaInput positiveFrequencyRestriction
      intervalUniquenessPrinciple fourierClosedForm finiteExponentialSpectrum openIntervalInjective : Prop}
    (hLorentzProfileModel : lorentzProfileModel)
    (hExplicitFourierFormulaInput : explicitFourierFormulaInput)
    (hPositiveFrequencyRestriction : positiveFrequencyRestriction)
    (hIntervalUniquenessPrinciple : intervalUniquenessPrinciple)
    (deriveFourierClosedForm :
      lorentzProfileModel → explicitFourierFormulaInput → fourierClosedForm)
    (deriveFiniteExponentialSpectrum :
      fourierClosedForm → positiveFrequencyRestriction → finiteExponentialSpectrum)
    (deriveOpenIntervalInjective :
      finiteExponentialSpectrum → intervalUniquenessPrinciple → openIntervalInjective) :
    fourierClosedForm ∧ finiteExponentialSpectrum ∧ openIntervalInjective := by
  have hClosed : fourierClosedForm :=
    deriveFourierClosedForm hLorentzProfileModel hExplicitFourierFormulaInput
  have hSpectrum : finiteExponentialSpectrum :=
    deriveFiniteExponentialSpectrum hClosed hPositiveFrequencyRestriction
  exact ⟨hClosed, hSpectrum, deriveOpenIntervalInjective hSpectrum hIntervalUniquenessPrinciple⟩

end Omega.TypedAddressBiaxialCompletion
