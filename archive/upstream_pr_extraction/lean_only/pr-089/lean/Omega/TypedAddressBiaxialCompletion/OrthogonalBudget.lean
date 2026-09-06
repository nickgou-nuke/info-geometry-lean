import Omega.TypedAddressBiaxialCompletion.OrthogonalSlice

namespace Omega.TypedAddressBiaxialCompletion

/-- The three typed-address biaxial-completion budgets are non-compensating when failure on any
single axis already blocks legal readout despite the other two axes passing. -/
def typedAddressBiaxialCompletionOrthogonalBudget
    (legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed : Prop) : Prop :=
  ((registerBudgetPassed ∧ modeBudgetPassed ∧ ¬ visibleBudgetPassed) → ¬ legalReadout) ∧
    ((visibleBudgetPassed ∧ modeBudgetPassed ∧ ¬ registerBudgetPassed) → ¬ legalReadout) ∧
    ((visibleBudgetPassed ∧ registerBudgetPassed ∧ ¬ modeBudgetPassed) → ¬ legalReadout)

/-- Packaging of the orthogonal-slice theorem: once legal readout forces the visible, register,
and mode budgets simultaneously, the three axes cannot compensate for one another.
    cor:typed-address-biaxial-completion-orthogonal-budget -/
theorem paper_typed_address_biaxial_completion_orthogonal_budget
    (legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed : Prop)
    (hVisibleRequired : legalReadout → visibleBudgetPassed)
    (hRegisterRequired : legalReadout → registerBudgetPassed)
    (hModeRequired : legalReadout → modeBudgetPassed) :
    typedAddressBiaxialCompletionOrthogonalBudget legalReadout visibleBudgetPassed
      registerBudgetPassed modeBudgetPassed := by
  have hAllBudgets : legalReadout →
      visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed := by
    intro hLegal
    exact ⟨hVisibleRequired hLegal, hRegisterRequired hLegal, hModeRequired hLegal⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hRegister, hMode, hNotVisible⟩ hLegal
    exact hNotVisible (hAllBudgets hLegal).1
  · rintro ⟨hVisible, hMode, hNotRegister⟩ hLegal
    exact hNotRegister (hAllBudgets hLegal).2.1
  · rintro ⟨hVisible, hRegister, hNotMode⟩ hLegal
    exact hNotMode (hAllBudgets hLegal).2.2

end Omega.TypedAddressBiaxialCompletion
