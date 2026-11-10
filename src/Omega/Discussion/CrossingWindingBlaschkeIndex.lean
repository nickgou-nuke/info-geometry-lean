import Mathlib.Tactic

namespace Omega.Discussion

/-!
# Integer defect-index sign classification

This owner formalizes the arithmetic content of a signed integer defect index.
It does not construct analytic crossing events, winding numbers, or Blaschke
products; those require additional carriers and maps. -/

/-- Signed integer attached to the concrete defect-index model. -/
def pointDefectIndex (κ : ℤ) : ℤ := κ

/-- A defect is visible when its integer index is nonzero. -/
def pointDefectVisible (κ : ℤ) : Prop :=
  pointDefectIndex κ ≠ 0

/-- The index has exactly one of three signs.  Visibility is equivalent to the
strictly positive or strictly negative cases, so the zero case is the unique
invisible case.  The cases are pairwise disjoint. -/
theorem point_defect_index_sign_partition (κ : ℤ) :
    ((pointDefectIndex κ = 0 ∧ ¬ pointDefectVisible κ) ∨
      (0 < pointDefectIndex κ ∧ pointDefectVisible κ) ∨
      (pointDefectIndex κ < 0 ∧ pointDefectVisible κ)) ∧
    ¬ (pointDefectIndex κ = 0 ∧ 0 < pointDefectIndex κ) ∧
    ¬ (pointDefectIndex κ = 0 ∧ pointDefectIndex κ < 0) ∧
    ¬ (0 < pointDefectIndex κ ∧ pointDefectIndex κ < 0) := by
  simp only [pointDefectIndex, pointDefectVisible]
  omega

end Omega.Discussion
