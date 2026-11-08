import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CompletenessGapAudit
import Omega.TypedAddressBiaxialCompletion.NonNullRequiresThreeAxes
import Omega.TypedAddressBiaxialCompletion.UnifiedRejectionRule

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper label: `cor:typed-address-biaxial-completion-unified-rejection-rule`.
If a finite audit still sits inside the completeness gap and no external mode-axis witness is
available, then the unified verifier can retain the local address/defect/endpoint package but
must output `null` rather than promote the finite certificate to a global statement. -/
theorem paper_typed_address_biaxial_completion_unified_rejection_rule_corollary
    (U : UnifiedRejectionWitness) (A : TypedAddressThreeAxisData)
    (nullReadout modeStabilityCert residueQuotaCert endpointResolutionGate : Prop)
    (nullImpliesModeStability : nullReadout → modeStabilityCert)
    (nullImpliesResidueQuota : nullReadout → residueQuotaCert)
    (nullImpliesEndpointResolution : nullReadout → endpointResolutionGate)
    (hUnitarySliceLocked : U.defectCertificate.certificateLoop.unitarySliceLocked)
    (hReadout :
      A.nonNullReadout ↔
        U.boundaryVerifier.verifierResult = BoundaryVerifierResult.certificate)
    (hNoModeAxis : ¬ A.modeAxisPassed) (hNullAudit : nullReadout) :
    U.addressConsistency ∧
      U.defectCompilation ∧
      U.toeplitzPsdEndpointBranch ∧
      modeStabilityCert ∧ residueQuotaCert ∧ endpointResolutionGate ∧
      U.boundaryVerifier.verifierResult = BoundaryVerifierResult.null := by
  have hUnified :=
    paper_typed_address_biaxial_completion_unified_rejection_rule U hUnitarySliceLocked
  have hGap := paper_typed_address_biaxial_completion_completeness_gap_audit
    nullReadout modeStabilityCert residueQuotaCert endpointResolutionGate
    nullImpliesModeStability nullImpliesResidueQuota nullImpliesEndpointResolution hNullAudit
  have hRejectCert :
      U.boundaryVerifier.verifierResult ≠ BoundaryVerifierResult.certificate := by
    intro hcert
    have hnonnull : A.nonNullReadout := hReadout.mpr hcert
    have haxes := paper_typed_address_biaxial_completion_nonnull_requires_three_axes A hnonnull
    exact hNoModeAxis haxes.2.2
  have hnull : U.boundaryVerifier.verifierResult = BoundaryVerifierResult.null := by
    cases hres : U.boundaryVerifier.verifierResult with
    | null =>
        rfl
    | certificate =>
        exact (hRejectCert hres).elim
  exact ⟨hUnified.1, hUnified.2.1, hUnified.2.2, hGap.1, hGap.2.1, hGap.2.2, hnull⟩

end Omega.TypedAddressBiaxialCompletion
