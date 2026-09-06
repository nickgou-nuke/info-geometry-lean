import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- The four contraction hypotheses suffice to collapse the rough resource geometry to a local
metric wrapper.
    prop:typed-address-biaxial-completion-classical-contraction -/
theorem paper_typed_address_biaxial_completion_classical_contraction
    {finiteComparableCost symmetricScalarCollapse localResidualAbsorbable budgetAbsorbable
        contractsToLocalMetricGeometry : Prop}
    (contractionWitness :
      finiteComparableCost ∧ symmetricScalarCollapse ∧ localResidualAbsorbable ∧ budgetAbsorbable →
        contractsToLocalMetricGeometry) :
    finiteComparableCost ∧ symmetricScalarCollapse ∧ localResidualAbsorbable ∧ budgetAbsorbable →
      contractsToLocalMetricGeometry := by
  exact contractionWitness

end Omega.TypedAddressBiaxialCompletion
