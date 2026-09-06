import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the first-layer extraction argument in comoving horizon scanning.
It reuses the typed-address Fourier closed-form package, then records the depth-grouping,
smallest-depth factorization, and tail-gap control needed to separate and recover the first layer.
-/
structure ComovingHorizonScanFirstLayerExtractionData where
  fourierClosedData : Omega.TypedAddressBiaxialCompletion.ComovingFourierClosedData
  explicitFourierDecomposition : Prop
  depthGroupedSpectrum : Prop
  smallestDepthExponentialFactored : Prop
  nextDepthGapTailBound : Prop
  leadingAsymptoticSeparation : Prop
  leadingLayerRecovered : Prop
  deriveLeadingAsymptoticSeparation :
    fourierClosedData.fourierClosedForm →
      explicitFourierDecomposition →
        depthGroupedSpectrum →
          smallestDepthExponentialFactored →
            nextDepthGapTailBound → leadingAsymptoticSeparation
  recoverLeadingLayer :
    leadingAsymptoticSeparation →
      fourierClosedData.finiteExponentialSpectrum →
        fourierClosedData.openIntervalInjective → leadingLayerRecovered

/-- Paper-facing wrapper for the comoving horizon first-layer extraction theorem: the Fourier
closed form is grouped by depth, the smallest depth is factored out, the tail is bounded by the
next depth gap, and finite exponential uniqueness recovers the leading layer.
    thm:cdim-comoving-horizon-scan-first-layer-extraction -/
theorem paper_cdim_comoving_horizon_scan_first_layer_extraction
    (D : ComovingHorizonScanFirstLayerExtractionData)
    (hExplicitFourierDecomposition : D.explicitFourierDecomposition)
    (hDepthGroupedSpectrum : D.depthGroupedSpectrum)
    (hSmallestDepthExponentialFactored : D.smallestDepthExponentialFactored)
    (hNextDepthGapTailBound : D.nextDepthGapTailBound)
    (hLorentzProfileModel : D.fourierClosedData.lorentzProfileModel)
    (hExplicitFourierFormulaInput : D.fourierClosedData.explicitFourierFormulaInput)
    (hPositiveFrequencyRestriction : D.fourierClosedData.positiveFrequencyRestriction)
    (hIntervalUniquenessPrinciple : D.fourierClosedData.intervalUniquenessPrinciple) :
    D.leadingAsymptoticSeparation ∧ D.leadingLayerRecovered := by
  have hClosedPackage :
      D.fourierClosedData.fourierClosedForm ∧ D.fourierClosedData.finiteExponentialSpectrum ∧
        D.fourierClosedData.openIntervalInjective :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_fourier_closed
      D.fourierClosedData
      hLorentzProfileModel hExplicitFourierFormulaInput
      hPositiveFrequencyRestriction hIntervalUniquenessPrinciple
  rcases hClosedPackage with ⟨hClosed, hSpectrum, hInjective⟩
  have hLead : D.leadingAsymptoticSeparation :=
    D.deriveLeadingAsymptoticSeparation hClosed hExplicitFourierDecomposition
      hDepthGroupedSpectrum hSmallestDepthExponentialFactored hNextDepthGapTailBound
  exact ⟨hLead, D.recoverLeadingLayer hLead hSpectrum hInjective⟩

end Omega.CircleDimension
