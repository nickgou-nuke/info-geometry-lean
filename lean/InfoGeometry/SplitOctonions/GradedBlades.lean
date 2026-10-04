import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.SplitOctonions

variable (R : Type*) [CommRing R]
variable (V : Type*) [AddCommGroup V] [Module R V]

open ExteriorAlgebra

def IsIsotropic (Q : QuadraticForm R V) (v : V) : Prop :=
  Q v = 0

def IsotropicCone (Q : QuadraticForm R V) : Set V :=
  {v : V | IsIsotropic R V Q v}

def gradedSign (degA degB : ℕ) : R :=
  if (degA * degB) % 2 = 1 then -1 else 1

def gradedBracket (degA degB : ℕ) (A B : ExteriorAlgebra R V) : ExteriorAlgebra R V :=
  A * B - gradedSign R degA degB • (B * A)

def blade1 (v : V) : ExteriorAlgebra R V :=
  ι R v

lemma gradedSign_one_one : (gradedSign R 1 1) = -1 := by rfl

theorem gradedBracket_grade1 (u v : V) :
    gradedBracket R V 1 1 (blade1 R V u) (blade1 R V v) = blade1 R V u * blade1 R V v + blade1 R V v * blade1 R V u := by
  dsimp [gradedBracket]
  rw [gradedSign_one_one]
  simp only [neg_smul, one_smul, sub_neg_eq_add]

theorem blade1_sq_zero (k : V) :
    blade1 R V k * blade1 R V k = 0 :=
  ι_sq_zero k

theorem blade1_gradedBracket_self_zero (u v : V) :
    gradedBracket R V 1 1 (blade1 R V u) (blade1 R V v) = 0 := by
  rw [gradedBracket_grade1]
  dsimp [blade1]
  have h_sq : ι R (u + v) * ι R (u + v) = 0 := ι_sq_zero (u + v)
  rw [map_add, add_mul, mul_add, mul_add] at h_sq
  rw [ι_sq_zero u, ι_sq_zero v] at h_sq
  simp only [zero_add, add_zero] at h_sq
  exact h_sq

lemma blade1_swap_neg (u v : V) :
    blade1 R V u * blade1 R V v = - (blade1 R V v * blade1 R V u) := by
  have h := blade1_gradedBracket_self_zero R V u v
  rw [gradedBracket_grade1] at h
  exact eq_neg_of_add_eq_zero_left h

def blade2 (u v : V) : ExteriorAlgebra R V :=
  blade1 R V u * blade1 R V v

lemma gradedSign_two_two : (gradedSign R 2 2) = 1 := by rfl

theorem gradedBracket_grade2 (P Q : ExteriorAlgebra R V) :
    gradedBracket R V 2 2 P Q = P * Q - Q * P := by
  dsimp [gradedBracket]
  rw [gradedSign_two_two]
  simp only [one_smul]

theorem plucker_on_shell_quadric (u v : V) :
    blade2 R V u v * blade2 R V u v = 0 := by
  dsimp [blade2]
  have h_swap : blade1 R V v * blade1 R V u = - (blade1 R V u * blade1 R V v) := blade1_swap_neg R V v u
  calc (blade1 R V u * blade1 R V v) * (blade1 R V u * blade1 R V v)
    _ = blade1 R V u * (blade1 R V v * blade1 R V u) * blade1 R V v := by simp [mul_assoc]
    _ = blade1 R V u * -(blade1 R V u * blade1 R V v) * blade1 R V v := by rw [h_swap]
    _ = -(blade1 R V u * blade1 R V u) * (blade1 R V v * blade1 R V v) := by simp [mul_assoc]
    _ = 0 := by rw [blade1_sq_zero R V u]; simp

def blade3 (u v w : V) : ExteriorAlgebra R V :=
  blade1 R V u * blade1 R V v * blade1 R V w

theorem associator_left_alternating (u v : V) :
    blade3 R V u u v = 0 := by
  dsimp [blade3]
  calc blade1 R V u * blade1 R V u * blade1 R V v
    _ = (blade1 R V u * blade1 R V u) * blade1 R V v := by simp [mul_assoc]
    _ = 0 * blade1 R V v := by rw [blade1_sq_zero R V u]
    _ = 0 := by simp

theorem associator_right_alternating (u v : V) :
    blade3 R V u v v = 0 := by
  dsimp [blade3]
  calc blade1 R V u * blade1 R V v * blade1 R V v
    _ = blade1 R V u * (blade1 R V v * blade1 R V v) := by simp [mul_assoc]
    _ = blade1 R V u * 0 := by rw [blade1_sq_zero R V v]
    _ = 0 := by simp

theorem associator_swap_adjacent (u v w : V) :
    blade3 R V u v w = - blade3 R V v u w := by
  dsimp [blade3]
  have h_swap : blade1 R V u * blade1 R V v = - (blade1 R V v * blade1 R V u) := blade1_swap_neg R V u v
  calc blade1 R V u * blade1 R V v * blade1 R V w
    _ = (blade1 R V u * blade1 R V v) * blade1 R V w := by simp [mul_assoc]
    _ = -(blade1 R V v * blade1 R V u) * blade1 R V w := by rw [h_swap]
    _ = -(blade1 R V v * blade1 R V u * blade1 R V w) := by simp [mul_assoc]

theorem associator_swap_cyclic (u v w : V) :
    blade3 R V u v w = - blade3 R V u w v := by
  dsimp [blade3]
  have h_swap : blade1 R V v * blade1 R V w = - (blade1 R V w * blade1 R V v) := blade1_swap_neg R V v w
  calc blade1 R V u * blade1 R V v * blade1 R V w
    _ = blade1 R V u * (blade1 R V v * blade1 R V w) := by simp [mul_assoc]
    _ = blade1 R V u * -(blade1 R V w * blade1 R V v) := by rw [h_swap]
    _ = -(blade1 R V u * blade1 R V w * blade1 R V v) := by simp [mul_assoc]

theorem gradedBracket_grade1_grade2 (v : V) (P : ExteriorAlgebra R V) :
    gradedBracket R V 1 2 (blade1 R V v) P = blade1 R V v * P - P * blade1 R V v := by
  dsimp [gradedBracket, gradedSign]
  simp only [one_smul]

theorem kkt_truncation_right (u v : V) :
    blade2 R V u v * blade1 R V v = 0 := by
  dsimp [blade2]
  calc blade1 R V u * blade1 R V v * blade1 R V v
    _ = blade1 R V u * (blade1 R V v * blade1 R V v) := by simp [mul_assoc]
    _ = blade1 R V u * 0 := by rw [blade1_sq_zero R V v]
    _ = 0 := by simp

theorem kkt_truncation_left (u v : V) :
    blade1 R V u * blade2 R V u v = 0 := by
  dsimp [blade2]
  calc blade1 R V u * (blade1 R V u * blade1 R V v)
    _ = (blade1 R V u * blade1 R V u) * blade1 R V v := by simp [mul_assoc]
    _ = 0 * blade1 R V v := by rw [blade1_sq_zero R V u]
    _ = 0 := by simp

end InfoGeometry.SplitOctonions
