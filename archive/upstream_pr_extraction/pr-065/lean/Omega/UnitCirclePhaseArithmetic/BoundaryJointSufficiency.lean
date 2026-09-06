import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion

/-- Re-export of the chapter-local verifier output type. -/
abbrev UnitCircleBoundaryVerifierResult := BoundaryVerifierResult

/-- The unit-circle phase arithmetic chapter uses the same three-axis boundary verifier interface
as the typed-address biaxial completion chapter. -/
abbrev UnitCircleBoundaryJointVerifierData := BoundaryJointVerifierData

/-- Joint closure of the radius blindspot, address collision, and endpoint heat axes is sufficient
for the boundary verifier to emit a certificate, and each axis remains logically non-substitutable
when the other two pass.
    thm:unit-circle-boundary-joint-sufficiency -/
theorem paper_unit_circle_boundary_joint_sufficiency (D : UnitCircleBoundaryJointVerifierData)
    (hAccepts : D.radiusBlindspotClosed → D.addressCollisionClosed →
      D.endpointHeatClosed → D.toeplitzPsdPassed → D.verifierResult = .certificate)
    (hRadius : D.verifierResult = .certificate → D.radiusBlindspotClosed)
    (hAddress : D.verifierResult = .certificate → D.addressCollisionClosed)
    (hEndpoint : D.verifierResult = .certificate → D.endpointHeatClosed)
    (hRadiusNonSubstitutable : D.addressCollisionClosed → D.endpointHeatClosed →
      ¬ D.radiusBlindspotClosed → D.verifierResult ≠ .certificate)
    (hAddressNonSubstitutable : D.radiusBlindspotClosed → D.endpointHeatClosed →
      ¬ D.addressCollisionClosed → D.verifierResult ≠ .certificate)
    (hEndpointNonSubstitutable : D.radiusBlindspotClosed → D.addressCollisionClosed →
      ¬ D.endpointHeatClosed → D.verifierResult ≠ .certificate) :
    (D.radiusBlindspotClosed ∧ D.addressCollisionClosed ∧
        D.endpointHeatClosed ∧ D.toeplitzPsdPassed →
      D.verifierResult = .certificate) ∧
    ((D.addressCollisionClosed ∧ D.endpointHeatClosed ∧
        ¬ D.radiusBlindspotClosed) →
      D.verifierResult ≠ .certificate) ∧
    ((D.radiusBlindspotClosed ∧ D.endpointHeatClosed ∧
        ¬ D.addressCollisionClosed) →
      D.verifierResult ≠ .certificate) ∧
    ((D.radiusBlindspotClosed ∧ D.addressCollisionClosed ∧
        ¬ D.endpointHeatClosed) →
      D.verifierResult ≠ .certificate) := by
  rcases paper_typed_address_biaxial_completion_boundary_joint_sufficiency D
      hAccepts hRadius hAddress hEndpoint hRadiusNonSubstitutable
      hAddressNonSubstitutable hEndpointNonSubstitutable with
    ⟨hsufficient, _, hradius, haddress, hendpoint⟩
  exact ⟨hsufficient, hradius, haddress, hendpoint⟩

end Omega.UnitCirclePhaseArithmetic
