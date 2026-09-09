import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete finite-signature carrier for the Takesaki criterion. -/
structure TakesakiCriterionData where
  M : Type
  N : Set M
  modularFlow : ℝ → M → M
  expectationFlag : Bool
  zeroKnowledgeFlag : Bool
  factorizationFlag : Bool

/-- The expectation/modular-invariance equivalence and the Boolean factorization implication give
the stated Takesaki criterion. -/
theorem paper_op_algebra_takesaki_criterion
    (D : TakesakiCriterionData)
    (expectation_iff_modularInvariant :
      (D.expectationFlag = true) ↔
        ∀ t x, x ∈ D.N → D.modularFlow t x ∈ D.N)
    (factorization_of_expectation :
      D.expectationFlag = true →
        D.zeroKnowledgeFlag = D.factorizationFlag) :
    ((D.expectationFlag = true) ↔
      ∀ t x, x ∈ D.N → D.modularFlow t x ∈ D.N) ∧
      (D.expectationFlag = true →
        (D.zeroKnowledgeFlag = true ↔ D.factorizationFlag = true)) := by
  refine ⟨expectation_iff_modularInvariant, ?_⟩
  intro hExpectation
  have hEq : D.zeroKnowledgeFlag = D.factorizationFlag :=
    factorization_of_expectation hExpectation
  constructor <;> intro h <;> simpa [hEq] using h

end Omega.OperatorAlgebra
