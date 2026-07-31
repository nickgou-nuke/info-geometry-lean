import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency
import Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality
import Omega.TypedAddressBiaxialCompletion.ThreeEndBudget

namespace Omega.Conclusion

open Omega.TypedAddressBiaxialCompletion

/-- Concrete closure data used by the conclusion-level three-end package. -/
structure ThreeEndCertificateClosureData where
  toeplitzPsdClosed : Prop
  failureWitness : Prop
  failure_of_toeplitz : ¬ toeplitzPsdClosed → failureWitness

/-- Concrete visible/register/mode budget data used by the conclusion-level package. -/
structure ThreeEndCertificateBudgetData where
  legalReadout : Prop
  visibleBudgetPassed : Prop
  registerBudgetPassed : Prop
  modeBudgetPassed : Prop
  register_failure_obstructs :
    visibleBudgetPassed → modeBudgetPassed → ¬ registerBudgetPassed → ¬ legalReadout

/-- Explicit aggregate owner for the three independent certificate ends. The two conclusion
properties are carried together with their proof terms, so downstream theorems consume actual
propositions rather than fabricated evidence predicates. -/
structure ThreeEndCertificateOrthogonalityData where
  boundary : BoundaryJointVerifierData
  budget : ThreeEndCertificateBudgetData
  closure : ThreeEndCertificateClosureData
  factorsThroughProduct : Prop
  failuresAreOrthogonal : Prop
  h_factorsThroughProduct : factorsThroughProduct
  h_failuresAreOrthogonal : failuresAreOrthogonal

theorem paper_conclusion_three_end_certificate_orthogonality
    (boundary : BoundaryJointVerifierData)
    (hBoundaryAccepts : boundary.radiusBlindspotClosed → boundary.addressCollisionClosed →
      boundary.endpointHeatClosed → boundary.toeplitzPsdPassed →
        boundary.verifierResult = .certificate)
    (hBoundaryRadius : boundary.verifierResult = .certificate →
      boundary.radiusBlindspotClosed)
    (hBoundaryAddress : boundary.verifierResult = .certificate →
      boundary.addressCollisionClosed)
    (hBoundaryEndpoint : boundary.verifierResult = .certificate →
      boundary.endpointHeatClosed)
    (hBoundaryRadiusNonSubstitutable : boundary.addressCollisionClosed →
      boundary.endpointHeatClosed → ¬ boundary.radiusBlindspotClosed →
        boundary.verifierResult ≠ .certificate)
    (hBoundaryAddressNonSubstitutable : boundary.radiusBlindspotClosed →
      boundary.endpointHeatClosed → ¬ boundary.addressCollisionClosed →
        boundary.verifierResult ≠ .certificate)
    (hBoundaryEndpointNonSubstitutable : boundary.radiusBlindspotClosed →
      boundary.addressCollisionClosed → ¬ boundary.endpointHeatClosed →
        boundary.verifierResult ≠ .certificate)
    (radiusBudgetClosed addressBudgetClosed endpointBudgetClosed toeplitzPsdClosed : Prop)
    (verifierAccepts failureWitness : Prop)
    (accepts_of_jointClosure :
      radiusBudgetClosed -> addressBudgetClosed -> endpointBudgetClosed ->
        toeplitzPsdClosed -> verifierAccepts)
    (failure_of_radius : ¬ radiusBudgetClosed -> failureWitness)
    (failure_of_address : ¬ addressBudgetClosed -> failureWitness)
    (failure_of_endpoint : ¬ endpointBudgetClosed -> failureWitness)
    (failure_of_toeplitz : ¬ toeplitzPsdClosed -> failureWitness)
    (legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed : Prop)
    (visible_required : legalReadout → visibleBudgetPassed)
    (register_required : legalReadout → registerBudgetPassed)
    (mode_required : legalReadout → modeBudgetPassed)
    (visible_failure_obstructs :
      registerBudgetPassed → modeBudgetPassed → ¬ visibleBudgetPassed → ¬ legalReadout)
    (register_failure_obstructs :
      visibleBudgetPassed → modeBudgetPassed → ¬ registerBudgetPassed → ¬ legalReadout)
    (mode_failure_obstructs :
      visibleBudgetPassed → registerBudgetPassed → ¬ modeBudgetPassed → ¬ legalReadout) :
    ((boundary.radiusBlindspotClosed ∧
        boundary.addressCollisionClosed ∧
        boundary.endpointHeatClosed ∧ boundary.toeplitzPsdPassed ∧
        legalReadout ∧ radiusBudgetClosed ∧ addressBudgetClosed ∧
        endpointBudgetClosed ∧ toeplitzPsdClosed) →
      boundary.verifierResult = .certificate ∧
        visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed ∧ verifierAccepts) ∧
    (((boundary.addressCollisionClosed ∧ boundary.endpointHeatClosed ∧
        ¬ boundary.radiusBlindspotClosed) → boundary.verifierResult ≠ .certificate) ∧
      ((boundary.radiusBlindspotClosed ∧ boundary.endpointHeatClosed ∧
        ¬ boundary.addressCollisionClosed) → boundary.verifierResult ≠ .certificate) ∧
      ((boundary.radiusBlindspotClosed ∧ boundary.addressCollisionClosed ∧
        ¬ boundary.endpointHeatClosed) → boundary.verifierResult ≠ .certificate) ∧
      ((registerBudgetPassed ∧ modeBudgetPassed ∧ ¬ visibleBudgetPassed) →
        ¬ legalReadout) ∧
      ((visibleBudgetPassed ∧ modeBudgetPassed ∧ ¬ registerBudgetPassed) →
        ¬ legalReadout) ∧
      ((visibleBudgetPassed ∧ registerBudgetPassed ∧ ¬ modeBudgetPassed) →
        ¬ legalReadout) ∧
      ((¬ radiusBudgetClosed ∨ ¬ addressBudgetClosed ∨ ¬ endpointBudgetClosed ∨
        ¬ toeplitzPsdClosed) → failureWitness)) := by
  have hBoundary :=
    paper_typed_address_biaxial_completion_boundary_joint_sufficiency boundary
      hBoundaryAccepts hBoundaryRadius hBoundaryAddress hBoundaryEndpoint
      hBoundaryRadiusNonSubstitutable hBoundaryAddressNonSubstitutable
      hBoundaryEndpointNonSubstitutable
  have hBudget :=
    paper_typed_address_biaxial_completion_budget_orthogonality
      legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed
      visible_required register_required mode_required visible_failure_obstructs
      register_failure_obstructs mode_failure_obstructs
  have hClosure := paper_typed_address_biaxial_completion_three_end_budget
    radiusBudgetClosed addressBudgetClosed endpointBudgetClosed toeplitzPsdClosed
    verifierAccepts failureWitness accepts_of_jointClosure failure_of_radius failure_of_address
    failure_of_endpoint failure_of_toeplitz
  rcases hBoundary with ⟨hBoundaryAccepts, _, hBoundaryRadius, hBoundaryAddress,
    hBoundaryEndpoint⟩
  rcases hBudget with ⟨hBudgetPasses, hBudgetVisible, hBudgetRegister, hBudgetMode⟩
  rcases hClosure with ⟨hClosureAccepts, hClosureFailure⟩
  constructor
  · rintro ⟨hr, ha, he, hpsd, hlegal, hcr, hca, hce, hct⟩
    have hBoundaryCert : boundary.verifierResult = .certificate :=
      hBoundaryAccepts ⟨hr, ha, he, hpsd⟩
    have hBudgetAll :
        visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed :=
      hBudgetPasses hlegal
    have hClosureCert : verifierAccepts := hClosureAccepts ⟨hcr, hca, hce, hct⟩
    exact ⟨hBoundaryCert, hBudgetAll.1, hBudgetAll.2.1, hBudgetAll.2.2, hClosureCert⟩
  · exact ⟨hBoundaryRadius, hBoundaryAddress, hBoundaryEndpoint, hBudgetVisible,
      hBudgetRegister, hBudgetMode, hClosureFailure⟩

end Omega.Conclusion
