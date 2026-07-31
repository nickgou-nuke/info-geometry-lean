import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Legal typed-address readout is orthogonal in the visible/register/mode budgets: it forces all
three budgets to pass, and failure of any single axis cannot be compensated by the other two.
    prop:typed-address-biaxial-completion-budget-orthogonality -/
theorem paper_typed_address_biaxial_completion_budget_orthogonality
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
    (legalReadout → visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed) ∧
      ((registerBudgetPassed ∧ modeBudgetPassed ∧ ¬ visibleBudgetPassed) →
        ¬ legalReadout) ∧
      ((visibleBudgetPassed ∧ modeBudgetPassed ∧ ¬ registerBudgetPassed) →
        ¬ legalReadout) ∧
      ((visibleBudgetPassed ∧ registerBudgetPassed ∧ ¬ modeBudgetPassed) →
        ¬ legalReadout) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hlegal
    exact ⟨visible_required hlegal, register_required hlegal, mode_required hlegal⟩
  · rintro ⟨hregister, hmode, hvisible⟩
    exact visible_failure_obstructs hregister hmode hvisible
  · rintro ⟨hvisible, hmode, hregister⟩
    exact register_failure_obstructs hvisible hmode hregister
  · rintro ⟨hvisible, hregister, hmode⟩
    exact mode_failure_obstructs hvisible hregister hmode

end Omega.TypedAddressBiaxialCompletion
