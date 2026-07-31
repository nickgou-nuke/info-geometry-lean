import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the comoving horizon first-layer extraction theorem: the Fourier
closed form is grouped by depth, the smallest depth is factored out, the tail is bounded by the
next depth gap, and finite exponential uniqueness recovers the leading layer.
    thm:cdim-comoving-horizon-scan-first-layer-extraction -/
theorem paper_cdim_comoving_horizon_scan_first_layer_extraction
    {explicitFourierDecomposition depthGroupedSpectrum smallestDepthExponentialFactored
      nextDepthGapTailBound leadingAsymptoticSeparation leadingLayerRecovered : Prop}
    (hExplicitFourierDecomposition : explicitFourierDecomposition)
    (hDepthGroupedSpectrum : depthGroupedSpectrum)
    (hSmallestDepthExponentialFactored : smallestDepthExponentialFactored)
    (hNextDepthGapTailBound : nextDepthGapTailBound)
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
      finiteExponentialSpectrum → intervalUniquenessPrinciple → openIntervalInjective)
    (deriveLeadingAsymptoticSeparation :
      fourierClosedForm → explicitFourierDecomposition → depthGroupedSpectrum →
        smallestDepthExponentialFactored → nextDepthGapTailBound → leadingAsymptoticSeparation)
    (recoverLeadingLayer :
      leadingAsymptoticSeparation → finiteExponentialSpectrum → openIntervalInjective →
        leadingLayerRecovered) :
    leadingAsymptoticSeparation ∧ leadingLayerRecovered := by
  have hClosedPackage :
      fourierClosedForm ∧ finiteExponentialSpectrum ∧ openIntervalInjective :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_fourier_closed
      hLorentzProfileModel hExplicitFourierFormulaInput
      hPositiveFrequencyRestriction hIntervalUniquenessPrinciple
      deriveFourierClosedForm deriveFiniteExponentialSpectrum deriveOpenIntervalInjective
  rcases hClosedPackage with ⟨hClosed, hSpectrum, hInjective⟩
  have hLead : leadingAsymptoticSeparation :=
    deriveLeadingAsymptoticSeparation hClosed hExplicitFourierDecomposition
      hDepthGroupedSpectrum hSmallestDepthExponentialFactored hNextDepthGapTailBound
  exact ⟨hLead, recoverLeadingLayer hLead hSpectrum hInjective⟩

end Omega.CircleDimension
