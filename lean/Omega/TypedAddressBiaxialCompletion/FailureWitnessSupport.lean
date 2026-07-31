import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CompletenessGapAudit
import Omega.TypedAddressBiaxialCompletion.UniqueContinuousTransversal

namespace Omega.TypedAddressBiaxialCompletion

/-- Packaging of the witness-support statement: a `NULL` readout already carries the mode-stability
certificate from the completeness-gap audit, and the existing minimal-record-axis package forces
that witness onto the canonical record axis with no new continuous transversal.
    prop:typed-address-biaxial-completion-witness-support -/
theorem paper_typed_address_biaxial_completion_witness_support
    (nullReadout modeStabilityCert residueQuotaCert endpointResolutionGate : Prop)
    (nullImpliesModeStability : nullReadout → modeStabilityCert)
    (nullImpliesResidueQuota : nullReadout → residueQuotaCert)
    (nullImpliesEndpointResolution : nullReadout → endpointResolutionGate)
    (recordAxis : Omega.CircleDimension.MinimalRecordAxisData) :
    nullReadout →
      (modeStabilityCert ∧ recordAxis.initialObject) ∧
        recordAxis.uniqueContinuousTransverse := by
  intro hNull
  have hGap :
      modeStabilityCert ∧ residueQuotaCert ∧ endpointResolutionGate :=
    paper_typed_address_biaxial_completion_completeness_gap_audit
      nullReadout modeStabilityCert residueQuotaCert endpointResolutionGate
      nullImpliesModeStability nullImpliesResidueQuota nullImpliesEndpointResolution hNull
  have hAxis :
      recordAxis.initialObject ∧ recordAxis.uniqueContinuousTransverse ∧
        recordAxis.orthogonalExternalization :=
    Omega.CircleDimension.paper_cdim_minimal_record_axis recordAxis
  have hTrans :
      recordAxis.uniqueContinuousTransverse :=
    paper_typed_address_biaxial_completion_unique_continuous_transversal recordAxis
  exact ⟨⟨hGap.1, hAxis.1⟩, hTrans⟩

end Omega.TypedAddressBiaxialCompletion
