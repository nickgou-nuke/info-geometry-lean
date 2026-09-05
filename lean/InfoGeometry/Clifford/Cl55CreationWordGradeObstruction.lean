import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import Mathlib.Tactic

/-!
# Occupation grades of native five-mode creation words

This extends the actual `Cl55` CAR and `cl55GradeSubmodule` owners. No new
Clifford algebra, gamma matrices, or grading predicate is introduced.

A word in distinct creation operators is nonzero: a graded commutator with
its first annihilator strips that first creation operator. The occupation
grade is its length. In particular, the five-creation word has grade five,
not grade two. A contact five-grading is a different construction.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55CreationWordGradeObstruction

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra

/-- Ordered multiplication in the existing associative Clifford algebra. -/
def creationWord : List (Fin 5) → Cl55
  | [] => 1
  | i :: is => creation55 i * creationWord is

@[simp] theorem creationWord_nil : creationWord [] = 1 := rfl

@[simp] theorem creationWord_cons (i : Fin 5) (is : List (Fin 5)) :
    creationWord (i :: is) = creation55 i * creationWord is := rfl

/-- An annihilator anticommutes past a word which does not contain its mode. -/
theorem annihilation_slide (i : Fin 5) (is : List (Fin 5)) (hi : i ∉ is) :
    annihilation55 i * creationWord is =
      ((-1 : ℝ) ^ is.length) • (creationWord is * annihilation55 i) := by
  revert hi
  induction is with
  | nil => intro hi; simp
  | cons j js ih =>
      intro hi
      have hij : i ≠ j := by
        intro h
        apply hi
        simp [h]
      have hjs : i ∉ js := by
        intro h
        exact hi (List.mem_cons_of_mem j h)
      have hswap : annihilation55 i * creation55 j =
          -(creation55 j * annihilation55 i) :=
        eq_neg_of_add_eq_zero_left
          (by simpa [hij] using annihilation55_creation55_anticommutator_eq i j)
      calc
        annihilation55 i * creationWord (j :: js) =
            (annihilation55 i * creation55 j) * creationWord js := by
          simp only [creationWord_cons, mul_assoc]
        _ = -(creation55 j * (annihilation55 i * creationWord js)) := by
          rw [hswap]
          simp only [neg_mul, mul_assoc]
        _ = -(creation55 j *
            (((-1 : ℝ) ^ js.length) • (creationWord js * annihilation55 i))) := by
          rw [ih hjs]
        _ = ((-1 : ℝ) ^ (j :: js).length) •
            (creationWord (j :: js) * annihilation55 i) := by
          simp only [List.length_cons, pow_succ, mul_neg_one,
            neg_smul, mul_smul_comm, creationWord_cons, mul_assoc]

/-- The graded commutator removes the first mode of a distinct creation word. -/
theorem annihilation_strips_head (i : Fin 5) (is : List (Fin 5)) (hi : i ∉ is) :
    annihilation55 i * creationWord (i :: is) -
        ((-1 : ℝ) ^ (i :: is).length) •
          (creationWord (i :: is) * annihilation55 i) = creationWord is := by
  have hcar : annihilation55 i * creation55 i =
      1 - creation55 i * annihilation55 i :=
    eq_sub_of_add_eq (annihilation55_creation55_anticommutator i)
  calc
    annihilation55 i * creationWord (i :: is) -
          ((-1 : ℝ) ^ (i :: is).length) •
            (creationWord (i :: is) * annihilation55 i) =
        creationWord is - creation55 i * (annihilation55 i * creationWord is) -
          ((-1 : ℝ) ^ (i :: is).length) •
            ((creation55 i * creationWord is) * annihilation55 i) := by
      rw [creationWord_cons, ← mul_assoc (annihilation55 i) (creation55 i) (creationWord is), hcar]
      simp only [sub_mul, one_mul, mul_assoc]
    _ = creationWord is := by
      rw [annihilation_slide i is hi]
      simp only [List.length_cons, pow_succ, mul_neg_one, neg_smul,
        mul_smul_comm, mul_assoc]
      abel

/-- Nonzero words are proved from native CAR, not a matrix rank computation. -/
theorem creationWord_ne_zero (is : List (Fin 5)) (hi : is.Nodup) :
    creationWord is ≠ 0 := by
  revert hi
  induction is with
  | nil =>
      intro hi
      simpa only [creationWord_nil] using (one_ne_zero : (1 : Cl55) ≠ 0)
  | cons i is ih =>
      intro hi
      have hhead : i ∉ is := (List.nodup_cons.mp hi).1
      have htail : is.Nodup := (List.nodup_cons.mp hi).2
      intro hz
      have hstrip := annihilation_strips_head i is hhead
      rw [hz, mul_zero, zero_mul, smul_zero, sub_self] at hstrip
      exact ih htail hstrip.symm

/-- The existing number-operator grading assigns length to a creation word. -/
theorem creationWord_mem_grade (is : List (Fin 5)) :
    creationWord is ∈ cl55GradeSubmodule (is.length : ℤ) := by
  induction is with
  | nil =>
      change HasOperatorGrade numberOperator55 (1 : Cl55) 0
      simp [HasOperatorGrade]
  | cons i is ih =>
      have h := grade_mul (creation55_mem_grade_one i) ih
      simpa only [creationWord_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, add_comm] using h

/-- Distinct adjoint eigenvalues cannot label the same nonzero operator. -/
theorem grade_unique_of_ne_zero {X : Cl55} {r s : ℤ} (hX : X ≠ 0)
    (hr : X ∈ cl55GradeSubmodule r) (hs : X ∈ cl55GradeSubmodule s) : r = s := by
  change numberOperator55 * X - X * numberOperator55 = (r : ℝ) • X at hr
  change numberOperator55 * X - X * numberOperator55 = (s : ℝ) • X at hs
  have hz : ((r : ℝ) - (s : ℝ)) • X = 0 := by
    rw [sub_smul, ← hr, ← hs, sub_self]
  have hscalar : (r : ℝ) = (s : ℝ) :=
    sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hX)
  exact_mod_cast hscalar

/-- Centering the number operator by a scalar does not change its adjoint grades. -/
theorem scalarShift_grade_iff (c : ℝ) (X : Cl55) (k : ℤ) :
    HasOperatorGrade (numberOperator55 - c • (1 : Cl55)) X k ↔
      X ∈ cl55GradeSubmodule k := by
  have hcomm :
      (numberOperator55 - c • (1 : Cl55)) * X -
          X * (numberOperator55 - c • (1 : Cl55)) =
        numberOperator55 * X - X * numberOperator55 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  change _ = (k : ℝ) • X ↔ _ = (k : ℝ) • X
  rw [hcomm]

/-- The attachment's centered Cartan sum is the existing number operator minus `5/2`. -/
theorem centeredCartanSum_eq :
    (∑ i : Fin 5, mixedGenerator55 i i) =
      numberOperator55 - (5 / 2 : ℝ) • (1 : Cl55) := by
  simp only [mixedGenerator55, if_pos rfl, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, numberOperator55]
  module

/-- The top creation operator in the supplied ordering. -/
def topCreation : Cl55 := creationWord [0, 1, 2, 3, 4]

theorem topCreation_ne_zero : topCreation ≠ 0 := by
  apply creationWord_ne_zero
  decide

theorem topCreation_mem_grade_five : topCreation ∈ cl55GradeSubmodule 5 := by
  exact creationWord_mem_grade [0, 1, 2, 3, 4]

/-- A literal obstruction to calling the five-creation word a contact grade-two element. -/
theorem topCreation_not_grade_two : topCreation ∉ cl55GradeSubmodule 2 := by
  intro h
  have h52 := grade_unique_of_ne_zero topCreation_ne_zero topCreation_mem_grade_five h
  norm_num at h52

/-- The operator is outside every degree in the displayed five-grade window. -/
theorem topCreation_outside_five_grade_window (k : ℤ) (hk : k ≤ 2) :
    topCreation ∉ cl55GradeSubmodule k := by
  intro h
  have h5k := grade_unique_of_ne_zero topCreation_ne_zero topCreation_mem_grade_five h
  omega

/-- The same obstruction holds for the source's centered grading element. -/
theorem topCreation_not_centered_grade_two :
    ¬ HasOperatorGrade (∑ i : Fin 5, mixedGenerator55 i i) topCreation 2 := by
  rw [centeredCartanSum_eq, scalarShift_grade_iff]
  exact topCreation_not_grade_two

end InfoGeometry.Clifford.Cl55CreationWordGradeObstruction
