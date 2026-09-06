import Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:unit-circle-complete-phase-threshold-orthogonality`. -/
theorem paper_unit_circle_complete_phase_threshold_orthogonality :
    ∀ (legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed : Prop)
      (visible_required : legalReadout → visibleBudgetPassed)
      (register_required : legalReadout → registerBudgetPassed)
      (mode_required : legalReadout → modeBudgetPassed)
      (visible_failure_obstructs :
        registerBudgetPassed → modeBudgetPassed → ¬ visibleBudgetPassed → ¬ legalReadout)
      (register_failure_obstructs :
        visibleBudgetPassed → modeBudgetPassed → ¬ registerBudgetPassed → ¬ legalReadout)
      (mode_failure_obstructs :
        visibleBudgetPassed → registerBudgetPassed → ¬ modeBudgetPassed → ¬ legalReadout),
      (legalReadout → visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed) ∧
        ((registerBudgetPassed ∧ modeBudgetPassed ∧ ¬ visibleBudgetPassed) →
          ¬ legalReadout) ∧
        ((visibleBudgetPassed ∧ modeBudgetPassed ∧ ¬ registerBudgetPassed) →
          ¬ legalReadout) ∧
        ((visibleBudgetPassed ∧ registerBudgetPassed ∧ ¬ modeBudgetPassed) →
          ¬ legalReadout) := by
  intro legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed
    visible_required register_required mode_required visible_failure_obstructs
    register_failure_obstructs mode_failure_obstructs
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_budget_orthogonality
    legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed
    visible_required register_required mode_required visible_failure_obstructs
    register_failure_obstructs mode_failure_obstructs

end Omega.UnitCirclePhaseArithmetic
