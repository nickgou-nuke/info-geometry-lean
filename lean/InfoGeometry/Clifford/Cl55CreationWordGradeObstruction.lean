import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import Mathlib.Tactic

/-! The native five-mode creation word has occupation grade five.
    This is deliberately separate from any contact grading. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55CreationWordGradeObstruction

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra

def creationWord : List (Fin 5) → Cl55
  | [] => 1
  | i :: is => creation55 i * creationWord is

@[simp] theorem creationWord_nil : creationWord [] = 1 := rfl
@[simp] theorem creationWord_cons (i : Fin 5) (is : List (Fin 5)) :
    creationWord (i :: is) = creation55 i * creationWord is := rfl

theorem annihilation_slide (i : Fin 5) (is : List (Fin 5)) (hi : i ∉ is) :
    annihilation55 i * creationWord is =
      ((-1 : ℝ) ^ is.length) • (creationWord is * annihilation55 i) := by
  revert hi
  induction is with
  | nil => intro; simp
  | cons j js ih =>
      intro h
      have hij : i ≠ j := by
        intro e; exact h (by simp [e])
      have hjs : i ∉ js := by
        intro e; exact h (by simp [e])
      have hs : annihilation55 i * creation55 j =
          -(creation55 j * annihilation55 i) :=
        eq_neg_of_add_eq_zero_left
          (by simpa [hij] using annihilation55_creation55_anticommutator_eq i j)
      calc
        annihilation55 i * creationWord (j :: js) =
            (annihilation55 i * creation55 j) * creationWord js := by
              simp only [creationWord_cons, mul_assoc]
        _ = -(creation55 j * (annihilation55 i * creationWord js)) := by
              rw [hs]; simp only [neg_mul, mul_assoc]
        _ = -(creation55 j *
            (((-1 : ℝ) ^ js.length) • (creationWord js * annihilation55 i))) := by
              rw [ih hjs]
        _ = ((-1 : ℝ) ^ (j :: js).length) •
            (creationWord (j :: js) * annihilation55 i) := by
              simp only [List.length_cons, pow_succ, mul_neg_one, neg_smul,
                mul_smul_comm, creationWord_cons, mul_assoc]

theorem annihilation_strips_head (i : Fin 5) (is : List (Fin 5)) (hi : i ∉ is) :
    annihilation55 i * creationWord (i :: is) -
        ((-1 : ℝ) ^ (i :: is).length) •
          (creationWord (i :: is) * annihilation55 i) = creationWord is := by
  have hc : annihilation55 i * creation55 i =
      1 - creation55 i * annihilation55 i :=
    eq_sub_of_add_eq (annihilation55_creation55_anticommutator i)
  calc
    annihilation55 i * creationWord (i :: is) -
          ((-1 : ℝ) ^ (i :: is).length) •
            (creationWord (i :: is) * annihilation55 i) =
        creationWord is - creation55 i * (annihilation55 i * creationWord is) -
          ((-1 : ℝ) ^ (i :: is).length) •
            ((creation55 i * creationWord is) * annihilation55 i) := by
      rw [creationWord_cons, ← mul_assoc (annihilation55 i) (creation55 i) (creationWord is), hc]
      simp only [sub_mul, one_mul, mul_assoc]
    _ = creationWord is := by
      rw [annihilation_slide i is hi]
      simp only [List.length_cons, pow_succ, mul_neg_one, neg_smul,
        mul_smul_comm, mul_assoc]
      abel

theorem creationWord_ne_zero (is : List (Fin 5)) (hi : is.Nodup) :
    creationWord is ≠ 0 := by
  revert hi
  induction is with
  | nil => intro; simpa only [creationWord_nil] using (one_ne_zero : (1 : Cl55) ≠ 0)
  | cons i is ih =>
      intro hnd hz
      have hhead : i ∉ is := (List.nodup_cons.mp hnd).1
      have htail : is.Nodup := (List.nodup_cons.mp hnd).2
      have hs := annihilation_strips_head i is hhead
      rw [hz, mul_zero, zero_mul, smul_zero, sub_self] at hs
      exact ih htail hs.symm

theorem creationWord_mem_grade (is : List (Fin 5)) :
    creationWord is ∈ cl55GradeSubmodule (is.length : ℤ) := by
  induction is with
  | nil => change HasOperatorGrade numberOperator55 (1 : Cl55) 0; simp [HasOperatorGrade]
  | cons i is ih =>
      have h := grade_mul (creation55_mem_grade_one i) ih
      simpa only [creationWord_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, add_comm] using h

theorem grade_unique_of_ne_zero {X : Cl55} {r s : ℤ} (hX : X ≠ 0)
    (hr : X ∈ cl55GradeSubmodule r) (hs : X ∈ cl55GradeSubmodule s) : r = s := by
  change numberOperator55 * X - X * numberOperator55 = (r : ℝ) • X at hr
  change numberOperator55 * X - X * numberOperator55 = (s : ℝ) • X at hs
  have hz : ((r : ℝ) - (s : ℝ)) • X = 0 := by rw [sub_smul, ← hr, ← hs, sub_self]
  have : (r : ℝ) = (s : ℝ) := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hX)
  exact_mod_cast this

theorem scalarShift_grade_iff (c : ℝ) (X : Cl55) (k : ℤ) :
    HasOperatorGrade (numberOperator55 - c • (1 : Cl55)) X k ↔
      X ∈ cl55GradeSubmodule k := by
  have hcomm : (numberOperator55 - c • (1 : Cl55)) * X -
      X * (numberOperator55 - c • (1 : Cl55)) =
        numberOperator55 * X - X * numberOperator55 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  change _ = (k : ℝ) • X ↔ _ = (k : ℝ) • X
  rw [hcomm]

def topCreation : Cl55 := creationWord [0, 1, 2, 3, 4]

theorem topCreation_ne_zero : topCreation ≠ 0 := by
  apply creationWord_ne_zero
  decide

theorem topCreation_mem_grade_five : topCreation ∈ cl55GradeSubmodule 5 := by
  exact creationWord_mem_grade [0, 1, 2, 3, 4]

theorem topCreation_not_grade_two : topCreation ∉ cl55GradeSubmodule 2 := by
  intro h
  have := grade_unique_of_ne_zero topCreation_ne_zero topCreation_mem_grade_five h
  norm_num at this

theorem topCreation_outside_five_grade_window (k : ℤ) (hk : k ≤ 2) :
    topCreation ∉ cl55GradeSubmodule k := by
  intro h
  have h5k := grade_unique_of_ne_zero topCreation_ne_zero topCreation_mem_grade_five h
  omega

end InfoGeometry.Clifford.Cl55CreationWordGradeObstruction
