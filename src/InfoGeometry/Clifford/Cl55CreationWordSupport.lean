/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55CreationWordGradeObstruction

/-! Exact support and occupation grades of native Clifford creation words. -/

namespace InfoGeometry.Clifford.Cl55CreationWordGradeObstruction

open InfoGeometry.Clifford.Clifford55

theorem creation_mul_word_eq_zero_of_mem (i : Fin 5) (is : List (Fin 5))
    (hi : i ∈ is) : creation55 i * creationWord is = 0 := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
      rcases List.mem_cons.mp hi with hij | hij
      · subst j
        simp [creationWord_cons, ← mul_assoc]
      · have hs : creation55 i * creation55 j = -(creation55 j * creation55 i) :=
          eq_neg_of_add_eq_zero_left (creation55_anticommutator i j)
        rw [creationWord_cons, ← mul_assoc, hs, neg_mul, mul_assoc, ih hij,
          mul_zero, neg_zero]

theorem creationWord_eq_zero_of_not_nodup (is : List (Fin 5))
    (hi : ¬ is.Nodup) : creationWord is = 0 := by
  induction is with
  | nil => simp at hi
  | cons i is ih =>
      by_cases hm : i ∈ is
      · exact creation_mul_word_eq_zero_of_mem i is hm
      · have ht : ¬ is.Nodup := fun h => hi (List.nodup_cons.mpr ⟨hm, h⟩)
        simp [creationWord_cons, ih ht]

theorem creationWord_ne_zero_iff (is : List (Fin 5)) :
    creationWord is ≠ 0 ↔ is.Nodup := by
  constructor
  · intro h
    by_contra hn
    exact h (creationWord_eq_zero_of_not_nodup is hn)
  · exact creationWord_ne_zero is

theorem creationWord_mem_grade_iff (is : List (Fin 5)) (k : ℤ) :
    creationWord is ∈ cl55GradeSubmodule k ↔ ¬ is.Nodup ∨ k = (is.length : ℤ) := by
  by_cases hi : is.Nodup
  · constructor
    · intro hk
      exact Or.inr (grade_unique_of_ne_zero (creationWord_ne_zero is hi) hk
        (creationWord_mem_grade is))
    · rintro (hn | rfl)
      · exact (hn hi).elim
      · exact creationWord_mem_grade is
  · simp [creationWord_eq_zero_of_not_nodup is hi, hi]

end InfoGeometry.Clifford.Cl55CreationWordGradeObstruction
