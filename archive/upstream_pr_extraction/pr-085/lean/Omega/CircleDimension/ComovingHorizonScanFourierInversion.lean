import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed

namespace Omega.CircleDimension

/-- CircleDimension restatement of the comoving horizon scan Fourier inversion theorem: the scan
profile is taken to be integrable and analytic, the typed-address closed form yields the explicit
finite exponential decomposition, and finite-spectrum uniqueness gives open-interval inversion.
    thm:cdim-comoving-horizon-scan-fourier-inversion -/
theorem paper_cdim_comoving_horizon_scan_fourier_inversion
    {lorentzProfileModel explicitFourierFormulaInput positiveFrequencyRestriction
      intervalUniquenessPrinciple fourierClosedForm finiteExponentialSpectrum openIntervalInjective
      integrableAnalyticProfile explicitFourierSpectrumFormula finiteMultisetInjectivity : Prop}
    (hIntegrableAnalyticProfile : integrableAnalyticProfile)
    (hLorentzProfileModel : lorentzProfileModel)
    (hExplicitFourierFormulaInput : explicitFourierFormulaInput)
    (hPositiveFrequencyRestriction : positiveFrequencyRestriction)
    (hIntervalUniquenessPrinciple : intervalUniquenessPrinciple)
    (deriveFourierClosedForm :
      lorentzProfileModel → explicitFourierFormulaInput → fourierClosedForm)
    (deriveFiniteExponentialSpectrum :
      fourierClosedForm → positiveFrequencyRestriction → finiteExponentialSpectrum)
    (deriveOpenIntervalInjective :
      finiteExponentialSpectrum → intervalUniquenessPrinciple → openIntervalInjective)
    (deriveExplicitFourierSpectrumFormula :
      fourierClosedForm → explicitFourierSpectrumFormula)
    (deriveFiniteMultisetInjectivity :
      finiteExponentialSpectrum → openIntervalInjective → finiteMultisetInjectivity) :
    integrableAnalyticProfile ∧ explicitFourierSpectrumFormula ∧
      finiteMultisetInjectivity := by
  have hClosedPackage : fourierClosedForm ∧ finiteExponentialSpectrum ∧ openIntervalInjective :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_fourier_closed
      hLorentzProfileModel hExplicitFourierFormulaInput
      hPositiveFrequencyRestriction hIntervalUniquenessPrinciple
      deriveFourierClosedForm deriveFiniteExponentialSpectrum deriveOpenIntervalInjective
  rcases hClosedPackage with ⟨hClosed, hSpectrum, hInjective⟩
  exact ⟨hIntegrableAnalyticProfile, deriveExplicitFourierSpectrumFormula hClosed,
    deriveFiniteMultisetInjectivity hSpectrum hInjective⟩

end Omega.CircleDimension
