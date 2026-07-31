import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The expectation/modular-invariance equivalence and the Boolean factorization implication give
the stated Takesaki criterion. -/
theorem paper_op_algebra_takesaki_criterion
    {M : Type} (N : Set M) (modularFlow : ℝ → M → M)
    (expectationFlag zeroKnowledgeFlag factorizationFlag : Bool)
    (expectation_iff_modularInvariant :
      (expectationFlag = true) ↔
        ∀ t x, x ∈ N → modularFlow t x ∈ N)
    (factorization_of_expectation :
      expectationFlag = true → zeroKnowledgeFlag = factorizationFlag) :
    ((expectationFlag = true) ↔
      ∀ t x, x ∈ N → modularFlow t x ∈ N) ∧
      (expectationFlag = true →
        (zeroKnowledgeFlag = true ↔ factorizationFlag = true)) := by
  refine ⟨expectation_iff_modularInvariant, ?_⟩
  intro hExpectation
  have hEq : zeroKnowledgeFlag = factorizationFlag :=
    factorization_of_expectation hExpectation
  constructor <;> intro h <;> simpa [hEq] using h

end Omega.OperatorAlgebra
