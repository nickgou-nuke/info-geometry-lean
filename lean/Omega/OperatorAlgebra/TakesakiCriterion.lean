/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-!
# Boolean/Propositional Interface Wrapper for the Takesaki Criterion

This module packages Boolean flags (`expectationFlag`, `zeroKnowledgeFlag`,
`factorizationFlag`) over an arbitrary carrier `M`, subset `N`, and map
`modularFlow : ℝ → M → M`. The equivalence
`(expectationFlag = true) ↔ ∀ t x, x ∈ N → modularFlow t x ∈ N` and the
implication `factorization_of_expectation` are supplied directly as hypotheses
to `paper_op_algebra_takesaki_criterion`; no conditional expectation or von
Neumann subalgebra theorem is constructed or proved here.
-/

/-- Abstract carrier and Boolean flag packet for the Takesaki-criterion interface. -/
structure TakesakiCriterionData where
  M : Type
  N : Set M
  modularFlow : ℝ → M → M
  expectationFlag : Bool
  zeroKnowledgeFlag : Bool
  factorizationFlag : Bool

/-- Rewrites the supplied Boolean equality hypothesis `factorization_of_expectation` into a
`true ↔ true` equivalence, returning it paired with the supplied `expectation_iff_modularInvariant` hypothesis. -/
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
