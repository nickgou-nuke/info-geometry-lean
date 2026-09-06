import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/- Joint closure of four budgets forces acceptance; failure of any one yields the common witness. -/
theorem paper_typed_address_biaxial_completion_three_end_budget
    (radiusBudgetClosed addressBudgetClosed endpointBudgetClosed toeplitzPsdClosed : Prop)
    (verifierAccepts failureWitness : Prop)
    (accepts_of_jointClosure :
      radiusBudgetClosed -> addressBudgetClosed -> endpointBudgetClosed ->
        toeplitzPsdClosed -> verifierAccepts)
    (failure_of_radius : ¬ radiusBudgetClosed -> failureWitness)
    (failure_of_address : ¬ addressBudgetClosed -> failureWitness)
    (failure_of_endpoint : ¬ endpointBudgetClosed -> failureWitness)
    (failure_of_toeplitz : ¬ toeplitzPsdClosed -> failureWitness) :
    (radiusBudgetClosed ∧ addressBudgetClosed ∧ endpointBudgetClosed ∧ toeplitzPsdClosed ->
      verifierAccepts) ∧
      ((¬ radiusBudgetClosed ∨ ¬ addressBudgetClosed ∨ ¬ endpointBudgetClosed ∨
          ¬ toeplitzPsdClosed) -> failureWitness) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, ha, he, ht⟩
    exact accepts_of_jointClosure hr ha he ht
  · rintro (hr | ha | he | ht)
    · exact failure_of_radius hr
    · exact failure_of_address ha
    · exact failure_of_endpoint he
    · exact failure_of_toeplitz ht

end Omega.TypedAddressBiaxialCompletion
