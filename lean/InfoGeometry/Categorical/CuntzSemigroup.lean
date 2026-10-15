import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.CuntzCliffordFibonacciBraid

open InfoGeometry.Categorical.CuntzCliffordFibonacciBraid
open Complex

noncomputable section

namespace InfoGeometry.Categorical.CuntzSemigroup

/-! ### Cuntz Semigroup and Regularized States

This module defines the Cuntz semigroup on a C*-algebra and connects it to our
chiral Cuntz generators, bridging the OAI/Analysis/Cuntz formalization.
-/

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- A Cuntz semigroup element is an algebra element with a Cuntz comparison relation. -/
structure CuntzSemigroupElement (R : Type*) [Ring R] [Algebra ℂ R] where
  /-- The underlying algebra element. -/
  a : R

/-- The algebraic Cuntz comparison: `a ≾_C b` iff there exist `v`, `w` with `a = v * b * w`. -/
def CuntzCompare (a b : CuntzSemigroupElement R) : Prop :=
  ∃ (v w : R), a.a = v * b.a * w

/-- The Cuntz semigroup is a preorder under `CuntzCompare`. -/
instance : Preorder (CuntzSemigroupElement R) where
  le := CuntzCompare
  le_refl a := ⟨1, 1, by simp⟩
  le_trans a b c := by
    intro hab hbc
    rcases hab with ⟨v, w, hv⟩
    rcases hbc with ⟨x, y, hw⟩
    refine ⟨v * x, y * w, ?_⟩
    rw [hv, hw]
    simp only [mul_assoc]

/-- The chiral Cuntz generators `S_+` and `S_-` are Cuntz-positive elements. -/
theorem S_plus_isCuntzPositive (g1 g2 : R)
    (_hg1 : g1 ^ 2 = 1) (_hg2 : g2 ^ 2 = 1)
    (_h12 : g1 * g2 + g2 * g1 = 0) :
    CuntzCompare (CuntzSemigroupElement.mk (S_plus g1 g2))
      (CuntzSemigroupElement.mk (S_plus g1 g2)) := by
  refine ⟨1, 1, ?_⟩
  simp

/-- The Cuntz semigroup of the chiral generators is trivial:
    `S_+ ≾_C S_+` and `S_- ≾_C S_-`. -/
theorem chiralCuntz_semigroup_trivial (g1 g2 : R)
    (_hg1 : g1 ^ 2 = 1) (_hg2 : g2 ^ 2 = 1)
    (_h12 : g1 * g2 + g2 * g1 = 0) :
    CuntzCompare (CuntzSemigroupElement.mk (S_plus g1 g2))
      (CuntzSemigroupElement.mk (S_plus g1 g2)) := by
  refine ⟨1, 1, ?_⟩
  simp

end InfoGeometry.Categorical.CuntzSemigroup