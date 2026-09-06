import Omega.TypedAddressBiaxialCompletion.CertificateLoop
import Omega.TypedAddressBiaxialCompletion.UnifiedRejectionRule

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-level closure of the minimal typed-address interface: the unified rejection witness
supplies the concrete `Read_US`, defect-compilation, and Toeplitz/endpoint branches, while the
certificate loop contributes the two Toeplitz equivalences. The standardized failure witness is
carried as an explicit `Fact` instance so the wrapper closes the advertised branch rather than
re-proving an arbitrary proposition from no evidence. -/
theorem paper_typed_address_biaxial_completion_minimal_interface_closure
    (U : Omega.TypedAddressBiaxialCompletion.UnifiedRejectionWitness)
    (C : Omega.TypedAddressBiaxialCompletion.TypedAddressCertificateLoopData)
    (hUnifiedUnitarySliceLocked :
      U.defectCertificate.certificateLoop.unitarySliceLocked)
    {monotoneToEndpointAtom exponentialErrorBound minDepthFormula : Prop}
    (hMonotoneToEndpointAtom : monotoneToEndpointAtom)
    (hExponentialErrorBound : exponentialErrorBound)
    (deriveMinDepthFormula : monotoneToEndpointAtom → exponentialErrorBound → minDepthFormula)
    (hBoundaryAccepts : U.boundaryVerifier.radiusBlindspotClosed →
      U.boundaryVerifier.addressCollisionClosed → U.boundaryVerifier.endpointHeatClosed →
        U.boundaryVerifier.toeplitzPsdPassed →
          U.boundaryVerifier.verifierResult = .certificate)
    (hBoundaryRadius : U.boundaryVerifier.verifierResult = .certificate →
      U.boundaryVerifier.radiusBlindspotClosed)
    (hBoundaryAddress : U.boundaryVerifier.verifierResult = .certificate →
      U.boundaryVerifier.addressCollisionClosed)
    (hBoundaryEndpoint : U.boundaryVerifier.verifierResult = .certificate →
      U.boundaryVerifier.endpointHeatClosed)
    (hBoundaryRadiusNonSubstitutable : U.boundaryVerifier.addressCollisionClosed →
      U.boundaryVerifier.endpointHeatClosed → ¬ U.boundaryVerifier.radiusBlindspotClosed →
        U.boundaryVerifier.verifierResult ≠ .certificate)
    (hBoundaryAddressNonSubstitutable : U.boundaryVerifier.radiusBlindspotClosed →
      U.boundaryVerifier.endpointHeatClosed → ¬ U.boundaryVerifier.addressCollisionClosed →
        U.boundaryVerifier.verifierResult ≠ .certificate)
    (hBoundaryEndpointNonSubstitutable : U.boundaryVerifier.radiusBlindspotClosed →
      U.boundaryVerifier.addressCollisionClosed → ¬ U.boundaryVerifier.endpointHeatClosed →
        U.boundaryVerifier.verifierResult ≠ .certificate)
    (hUnitarySliceLocked : C.unitarySliceLocked)
    (standardizedFailureWitness : Prop) [Fact standardizedFailureWitness] :
    U.addressConsistency ∧ U.defectCompilation ∧
      U.toeplitzPsdEndpointBranch
        (monotoneToEndpointAtom := monotoneToEndpointAtom)
        (exponentialErrorBound := exponentialErrorBound)
        (minDepthFormula := minDepthFormula) ∧
      (C.repulsionRadiusTendsToOne ↔ C.toeplitzPsdAll) ∧
      (C.toeplitzPsdAll ↔ C.toeplitzPsdCofinal) ∧ standardizedFailureWitness := by
  have hUnified :=
    paper_typed_address_biaxial_completion_unified_rejection_rule U
      hMonotoneToEndpointAtom hExponentialErrorBound deriveMinDepthFormula
      hBoundaryAccepts hBoundaryRadius hBoundaryAddress hBoundaryEndpoint
      hBoundaryRadiusNonSubstitutable hBoundaryAddressNonSubstitutable
      hBoundaryEndpointNonSubstitutable hUnifiedUnitarySliceLocked
  have hLoop := paper_typed_address_biaxial_completion_certificate_loop C hUnitarySliceLocked
  exact ⟨hUnified.1, hUnified.2.1, hUnified.2.2, hLoop.2.2.1, hLoop.2.2.2, Fact.out⟩

end Omega.TypedAddressBiaxialCompletion
