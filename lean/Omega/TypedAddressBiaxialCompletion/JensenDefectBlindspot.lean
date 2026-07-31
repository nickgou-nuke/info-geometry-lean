import Mathlib.Tactic
import Omega.CircleDimension.ComovingHorizonScanFirstLayerExtraction
import Omega.CircleDimension.RadiusBlindspotJointDiscreteBudgetOrthogonal
import Omega.TypedAddressBiaxialCompletion.BoundaryAddressCollision
import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization
import Omega.TypedAddressBiaxialCompletion.OffsliceDichotomy

namespace Omega.TypedAddressBiaxialCompletion

open scoped BigOperators

/-- Paper-facing wrapper for the finite-radius Jensen-defect blindspot dichotomy: the finite-radius
readout carries the usual nonnegativity/zero-free equivalence, the radius blindspot and address
ledger remain orthogonal necessary resources, the comoving Fourier route gives the audited
recovery path, and any fixed-chart blindspot instance either enters that recovery path or yields a
null witness while still forcing an address-collision budget witness.
    prop:typed-address-biaxial-completion-jensen-defect-blindspot -/
theorem paper_typed_address_biaxial_completion_jensen_defect_blindspot
    {radiusBlindspotNecessary addressLedgerNecessary : Prop}
    (hRadiusBlindspot : radiusBlindspotNecessary)
    (hAddressLedger : addressLedgerNecessary)
    (J : JensenDefectFiniteizationData) {rho : ℝ} (hrho : 0 < rho) (hrho_lt : rho < 1)
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
        leadingLayerRecovered)
    (offsliceAssertion prefixRecoveryRoute nullBlindspotWitness noThirdPath : Prop)
    (hSplit : offsliceAssertion → prefixRecoveryRoute ∨ nullBlindspotWitness)
    (hNoThird : offsliceAssertion → noThirdPath)
    (c T : ℝ) (b : ℕ) (addressOccupancy : Fin (2 ^ b) → ℝ)
    (hNonneg : ∀ a, 0 ≤ addressOccupancy a)
    (hTotal : c * T^2 * Real.log T ≤ ∑ a, addressOccupancy a) :
    offsliceAssertion →
      (prefixRecoveryRoute ∨ nullBlindspotWitness) ∧
      noThirdPath ∧
      (0 ≤ J.defect rho ∧ (J.defect rho = 0 ↔ J.zeroFree rho)) ∧
      (radiusBlindspotNecessary ∧ addressLedgerNecessary) ∧
      (leadingAsymptoticSeparation ∧ leadingLayerRecovered) ∧
      ∃ a : Fin (2 ^ b), c * T^2 * Real.log T / (2 : ℝ) ^ b ≤ addressOccupancy a := by
  intro hOffslice
  have hOffsliceSplit :
      (prefixRecoveryRoute ∨ nullBlindspotWitness) ∧ noThirdPath :=
    paper_typed_address_biaxial_completion_offslice_dichotomy
      offsliceAssertion prefixRecoveryRoute nullBlindspotWitness noThirdPath hSplit hNoThird hOffslice
  have hJensen :
      0 ≤ J.defect rho ∧ (J.defect rho = 0 ↔ J.zeroFree rho) :=
    paper_typed_address_biaxial_completion_jensen_defect_finiteization J hrho hrho_lt
  have hBlindspot :
      radiusBlindspotNecessary ∧ addressLedgerNecessary :=
    Omega.CircleDimension.paper_cdim_radius_blindspot_and_joint_discrete_budget_orthogonal
      hRadiusBlindspot hAddressLedger
  have hRecovery :
      leadingAsymptoticSeparation ∧ leadingLayerRecovered :=
    Omega.CircleDimension.paper_cdim_comoving_horizon_scan_first_layer_extraction
      hExplicitFourierDecomposition hDepthGroupedSpectrum
      hSmallestDepthExponentialFactored hNextDepthGapTailBound
      hLorentzProfileModel hExplicitFourierFormulaInput
      hPositiveFrequencyRestriction hIntervalUniquenessPrinciple
      deriveFourierClosedForm deriveFiniteExponentialSpectrum deriveOpenIntervalInjective
      deriveLeadingAsymptoticSeparation recoverLeadingLayer
  rcases
      BoundaryAddressCollision.paper_typed_address_biaxial_completion_boundary_address_collision
        c T b addressOccupancy hNonneg hTotal with
    ⟨a, ha⟩
  exact ⟨hOffsliceSplit.1, hOffsliceSplit.2, hJensen, hBlindspot, hRecovery, a, ha⟩

end Omega.TypedAddressBiaxialCompletion
