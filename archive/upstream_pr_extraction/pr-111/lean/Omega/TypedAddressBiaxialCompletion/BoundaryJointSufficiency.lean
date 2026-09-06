import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Abstract output of the chapter-local boundary verifier. -/
inductive BoundaryVerifierResult where
  | null
  | certificate
  deriving DecidableEq

/-- Minimal interface for the joint sufficiency theorem: simultaneous closure of the three
boundary axes and the Toeplitz--PSD side condition yields a non-`NULL` certificate, while each
axis remains logically non-substitutable by the other two. -/
structure BoundaryJointVerifierData where
  radiusBlindspotClosed : Prop
  addressCollisionClosed : Prop
  endpointHeatClosed : Prop
  toeplitzPsdPassed : Prop
  verifierResult : BoundaryVerifierResult

/-- Joint closure of the radius, address, and endpoint-heat axes is sufficient for a non-`NULL`
boundary certificate, and none of the three axes can be replaced by the other two.
    thm:typed-address-biaxial-completion-boundary-joint-sufficiency -/
theorem paper_typed_address_biaxial_completion_boundary_joint_sufficiency
    (h : BoundaryJointVerifierData)
    (accepts_of_jointClosure :
      h.radiusBlindspotClosed → h.addressCollisionClosed →
        h.endpointHeatClosed → h.toeplitzPsdPassed →
          h.verifierResult = .certificate)
    (radius_required : h.verifierResult = .certificate → h.radiusBlindspotClosed)
    (address_required : h.verifierResult = .certificate → h.addressCollisionClosed)
    (endpoint_required : h.verifierResult = .certificate → h.endpointHeatClosed)
    (radius_non_substitutable :
      h.addressCollisionClosed → h.endpointHeatClosed →
        ¬ h.radiusBlindspotClosed → h.verifierResult ≠ .certificate)
    (address_non_substitutable :
      h.radiusBlindspotClosed → h.endpointHeatClosed →
        ¬ h.addressCollisionClosed → h.verifierResult ≠ .certificate)
    (endpoint_non_substitutable :
      h.radiusBlindspotClosed → h.addressCollisionClosed →
        ¬ h.endpointHeatClosed → h.verifierResult ≠ .certificate) :
    (h.radiusBlindspotClosed ∧ h.addressCollisionClosed ∧
        h.endpointHeatClosed ∧ h.toeplitzPsdPassed →
      h.verifierResult = .certificate) ∧
    (h.verifierResult = .certificate →
      h.radiusBlindspotClosed ∧ h.addressCollisionClosed ∧
        h.endpointHeatClosed) ∧
    ((h.addressCollisionClosed ∧ h.endpointHeatClosed ∧
        ¬ h.radiusBlindspotClosed) →
      h.verifierResult ≠ .certificate) ∧
    ((h.radiusBlindspotClosed ∧ h.endpointHeatClosed ∧
        ¬ h.addressCollisionClosed) →
      h.verifierResult ≠ .certificate) ∧
    ((h.radiusBlindspotClosed ∧ h.addressCollisionClosed ∧
        ¬ h.endpointHeatClosed) →
      h.verifierResult ≠ .certificate) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hr, ha, he, hpsd⟩
    exact accepts_of_jointClosure hr ha he hpsd
  · intro hcert
    exact ⟨radius_required hcert, address_required hcert, endpoint_required hcert⟩
  · rintro ⟨ha, he, hnotr⟩
    exact radius_non_substitutable ha he hnotr
  · rintro ⟨hr, he, hnota⟩
    exact address_non_substitutable hr he hnota
  · rintro ⟨hr, ha, hnote⟩
    exact endpoint_non_substitutable hr ha hnote

end Omega.TypedAddressBiaxialCompletion
