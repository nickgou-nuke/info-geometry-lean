import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality
import InfoGeometry.External.Automath.Omega.TypedAddressBiaxialCompletion.NullExhaustive
import InfoGeometry.External.Automath.Omega.TypedAddressBiaxialCompletion.UnitarySliceAddressClosure

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter theorem packaging the orthogonal-slice picture for typed-address biaxial completion:
the unitary-slice readout stays closed, any legal readout must pass the visible/register/mode
budgets simultaneously, and the `NULL` trichotomy is exhaustive. -/
theorem paper_typed_address_biaxial_completion_orthogonal_slice
    (U : UnitarySliceAddressClosureData) (B : BudgetOrthogonalityData)
    (N : TypedAddressNullTrichotomyData) :
    U.readUSClosed ∧
      (B.legalReadout → B.visibleBudgetPassed ∧ B.registerBudgetPassed ∧ B.modeBudgetPassed) ∧
      N.exhaustive := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_typed_address_biaxial_completion_unitary_slice_address_closure U
  · exact (paper_typed_address_biaxial_completion_budget_orthogonality B).1
  · exact N.exhaustiveWitness

end Omega.TypedAddressBiaxialCompletion
