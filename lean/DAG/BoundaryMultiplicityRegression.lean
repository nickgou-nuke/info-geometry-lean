/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.SelfLoopIncidenceRegression
import Mathlib.Tactic

/-!
# Repeated-index boundary regression

Boundary coefficients are signed sums over occurrences. Priority conditionals
lose multiplicity when a face or digon repeats an edge index. -/
namespace DAG.BoundaryMultiplicityRegression

open SelfLoopIncidenceRegression

/-- The pre-repair priority formulas, defined here only to make the regression
comparison explicit. -/
def oldFacePriorityCoeff (e1 e2 e3 j : Nat) : ℚ :=
  if j = e1 then 1 else if j = e2 then 1 else if j = e3 then -1 else 0

def oldDigonPriorityCoeff (eU eV j : Nat) : ℚ :=
  if j = eU then 1 else if j = eV then 1 else 0

/-- The face coefficient is exactly the signed sum of its edge occurrences. -/
theorem face_coefficient_is_occurrence_sum (e1 e2 e3 j : Nat) :
    DAG.faceBoundaryCoeff e1 e2 e3 j =
      (if j = e1 then (1 : ℚ) else 0) +
      (if j = e2 then 1 else 0) -
      (if j = e3 then 1 else 0) := by
  unfold DAG.faceBoundaryCoeff
  split_ifs <;> norm_num

/-- The digon coefficient is the sum of both positive edge occurrences. -/
theorem digon_coefficient_is_occurrence_sum (eU eV j : Nat) :
    DAG.digonBoundaryCoeff eU eV j =
      (if j = eU then (1 : ℚ) else 0) + (if j = eV then 1 else 0) := by
  unfold DAG.digonBoundaryCoeff
  split_ifs <;> norm_num

/-- A malformed payload used to expose priority-vs-occurrence-sum behavior. -/
def repeatedFace : TwoComplex Nat :=
  { oneLoop with
    edges := #[(0, 1), (1, 0)]
    faces := #[(0, 0, 1)] }

/-- The old priority rule counts only the first occurrence of edge zero. -/
theorem old_face_priority_loses_multiplicity :
    oldFacePriorityCoeff 0 0 1 0 = 1 := by
  norm_num [oldFacePriorityCoeff]

/-- The signed occurrence sum records both positive occurrences. -/
theorem repeated_face_coefficient_is_two :
    DAG.faceBoundaryCoeff 0 0 1 0 = 2 := by
  norm_num [DAG.faceBoundaryCoeff]

/-- The matrix boundary implementation uses the corrected coefficient. -/
theorem repeated_face_matrix_entry_is_two :
    DAG.boundary2Matrix repeatedFace (⟨0, by decide⟩ : Fin 1)
      (⟨0, by decide⟩ : Fin 2) = 2 := by
  norm_num [DAG.boundary2Matrix, DAG.faceBoundaryCoeff, repeatedFace,
    oneLoop, SelfLoopIncidenceRegression.oneLoop]

/-- Both occurrences in a repeated digon edge contribute positively. -/
theorem repeated_digon_coefficient_is_two :
    DAG.digonBoundaryCoeff 0 0 0 = 2 := by
  norm_num [DAG.digonBoundaryCoeff]

/-- The old digon priority rule likewise discarded its repeated occurrence. -/
theorem old_digon_priority_loses_multiplicity :
    oldDigonPriorityCoeff 0 0 0 = 1 := by
  norm_num [oldDigonPriorityCoeff]

end DAG.BoundaryMultiplicityRegression
