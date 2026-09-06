import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CompletenessGapAudit
import Omega.TypedAddressBiaxialCompletion.UniqueContinuousTransversal

namespace Omega.TypedAddressBiaxialCompletion

/-- Packaging of the support statement: a `NULL` readout already carries the mode-stability
certificate from the completeness-gap audit, and the existing minimal-record-axis package forces
that conclusion onto the canonical record axis with no new continuous transversal.
    prop:typed-address-biaxial-completion-support -/
theorem typed_address_biaxial_completion_support
    (nullReadout modeStabilityCert residueQuotaCert endpointResolutionGate : Prop)
    (nullImpliesModeStability : nullReadout → modeStabilityCert)
    (nullImpliesResidueQuota : nullReadout → residueQuotaCert)
    (nullImpliesEndpointResolution : nullReadout → endpointResolutionGate)
    {initialObject uniqueContinuousTransverse orthogonalExternalization : Prop}
    (hInitial : initialObject)
    (hUnique : uniqueContinuousTransverse)
    (hOrthogonal : orthogonalExternalization) :
    nullReadout →
      (modeStabilityCert ∧ initialObject) ∧ uniqueContinuousTransverse := by
  intro hNull
  have hGap :
      modeStabilityCert ∧ residueQuotaCert ∧ endpointResolutionGate :=
    paper_typed_address_biaxial_completion_completeness_gap_audit
      nullReadout modeStabilityCert residueQuotaCert endpointResolutionGate
      nullImpliesModeStability nullImpliesResidueQuota nullImpliesEndpointResolution hNull
  have hAxis : initialObject ∧ uniqueContinuousTransverse ∧ orthogonalExternalization :=
    Omega.CircleDimension.paper_cdim_minimal_record_axis hInitial hUnique hOrthogonal
  exact ⟨⟨hGap.1, hAxis.1⟩, hAxis.2.1⟩

end Omega.TypedAddressBiaxialCompletion
