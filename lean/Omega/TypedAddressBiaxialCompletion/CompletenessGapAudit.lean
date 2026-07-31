import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- A `NULL` readout packages the biaxial completeness gap into the three advertised audit gates.
    prop:typed-address-biaxial-completion-completeness-gap-audit -/
theorem paper_typed_address_biaxial_completion_completeness_gap_audit
    (nullReadout modeStabilityCert residueQuotaCert endpointResolutionGate : Prop)
    (nullImpliesModeStability : nullReadout → modeStabilityCert)
    (nullImpliesResidueQuota : nullReadout → residueQuotaCert)
    (nullImpliesEndpointResolution : nullReadout → endpointResolutionGate) :
    nullReadout → modeStabilityCert ∧ residueQuotaCert ∧ endpointResolutionGate := by
  intro hnull
  exact
    ⟨nullImpliesModeStability hnull, nullImpliesResidueQuota hnull,
      nullImpliesEndpointResolution hnull⟩

end Omega.TypedAddressBiaxialCompletion
