import Omega.TypedAddressBiaxialCompletion.BoundaryEndpointHeat
import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency

namespace Omega.TypedAddressBiaxialCompletion

/-- The endpoint-heat budget contributes its own paper-facing heat wrapper, and it is
logically non-substitutable even when the radius blindspot and address collision axes are
already closed.
    cor:typed-address-biaxial-completion-boundary-endpoint-orthogonal -/
theorem paper_typed_address_biaxial_completion_boundary_endpoint_orthogonal
    {monotoneToEndpointAtom exponentialErrorBound minDepthFormula : Prop}
    (hMonotoneToEndpointAtom : monotoneToEndpointAtom)
    (hExponentialErrorBound : exponentialErrorBound)
    (deriveMinDepthFormula : monotoneToEndpointAtom → exponentialErrorBound → minDepthFormula)
    (V : BoundaryJointVerifierData)
    (hAccepts : V.radiusBlindspotClosed → V.addressCollisionClosed →
      V.endpointHeatClosed → V.toeplitzPsdPassed → V.verifierResult = .certificate)
    (hRadius : V.verifierResult = .certificate → V.radiusBlindspotClosed)
    (hAddress : V.verifierResult = .certificate → V.addressCollisionClosed)
    (hEndpoint : V.verifierResult = .certificate → V.endpointHeatClosed)
    (hRadiusNonSubstitutable : V.addressCollisionClosed → V.endpointHeatClosed →
      ¬ V.radiusBlindspotClosed → V.verifierResult ≠ .certificate)
    (hAddressNonSubstitutable : V.radiusBlindspotClosed → V.endpointHeatClosed →
      ¬ V.addressCollisionClosed → V.verifierResult ≠ .certificate)
    (hEndpointNonSubstitutable : V.radiusBlindspotClosed → V.addressCollisionClosed →
      ¬ V.endpointHeatClosed → V.verifierResult ≠ .certificate) :
    (monotoneToEndpointAtom ∧ exponentialErrorBound ∧ minDepthFormula) ∧
      ((V.radiusBlindspotClosed ∧ V.addressCollisionClosed ∧
          ¬ V.endpointHeatClosed) →
        V.verifierResult ≠ BoundaryVerifierResult.certificate) := by
  refine ⟨paper_typed_address_biaxial_completion_boundary_endpoint_heat
    hMonotoneToEndpointAtom hExponentialErrorBound deriveMinDepthFormula, ?_⟩
  exact (paper_typed_address_biaxial_completion_boundary_joint_sufficiency V
    hAccepts hRadius hAddress hEndpoint hRadiusNonSubstitutable
    hAddressNonSubstitutable hEndpointNonSubstitutable).2.2.2.2

end Omega.TypedAddressBiaxialCompletion
