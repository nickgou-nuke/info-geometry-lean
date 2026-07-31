import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality
import Omega.TypedAddressBiaxialCompletion.NullExhaustive
import Omega.TypedAddressBiaxialCompletion.UnitarySliceAddressClosure

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter theorem packaging the orthogonal-slice picture for typed-address biaxial completion:
the unitary-slice readout stays closed, any legal readout must pass the visible/register/mode
budgets simultaneously, and the `NULL` trichotomy is exhaustive. -/
theorem paper_typed_address_biaxial_completion_orthogonal_slice
    (U : UnitarySliceAddressClosureData) (N : TypedAddressNullTrichotomyData)
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
    U.readUSClosed ∧
      (legalReadout → visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed) ∧
      N.exhaustive := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_typed_address_biaxial_completion_unitary_slice_address_closure U
  · exact (paper_typed_address_biaxial_completion_budget_orthogonality
      legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed
      visible_required register_required mode_required visible_failure_obstructs
      register_failure_obstructs mode_failure_obstructs).1
  · exact N.exhaustiveWitness

end Omega.TypedAddressBiaxialCompletion
