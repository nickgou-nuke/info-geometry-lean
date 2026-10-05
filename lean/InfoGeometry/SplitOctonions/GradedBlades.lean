import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Exterior-algebra blades and split-signature quadratic forms

This file's `blade3` is a product in Mathlib's associative exterior algebra.
Its alternating identities are wedge-product identities, not identities for
the nonassociative split-octonion associator. The quadratic-form cone and the
exterior-algebra blades are separate carriers here. Associativity is inherited
from the exterior-algebra multiplication (`mul_assoc`); no local associator
wrapper is needed or used as a split-octonion law.
-/

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

theorem blade1_sq_zero (k : V) :
    blade1 R V k * blade1 R V k = 0 :=
  ι_sq_zero k

theorem blade1_gradedBracket_self_zero (u v : V) :
    gradedBracket R V 1 1 (blade1 R V u) (blade1 R V v) = 0 := by
  simpa [gradedBracket, gradedSign, blade1, sub_eq_add_neg] using
    (ExteriorAlgebra.ι_add_mul_swap (R := R) u v)

lemma blade1_swap_neg (u v : V) :
    blade1 R V u * blade1 R V v = - (blade1 R V v * blade1 R V u) := by
  have h := blade1_gradedBracket_self_zero R V u v
  simpa [gradedBracket, gradedSign, blade1, sub_eq_add_neg] using
    (eq_neg_of_add_eq_zero_left
      (show blade1 R V u * blade1 R V v + blade1 R V v * blade1 R V u = 0 by
        simpa [gradedBracket, gradedSign, blade1, sub_eq_add_neg] using h))

def blade2 (u v : V) : ExteriorAlgebra R V :=
  blade1 R V u * blade1 R V v

theorem decomposable_blade2_wedge_square_zero (u v : V) :
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

theorem blade3_left_alternating (u v : V) :
    blade3 R V u u v = 0 := by
  dsimp [blade3]
  calc blade1 R V u * blade1 R V u * blade1 R V v
    _ = (blade1 R V u * blade1 R V u) * blade1 R V v := by simp [mul_assoc]
    _ = 0 * blade1 R V v := by rw [blade1_sq_zero R V u]
    _ = 0 := by simp

theorem blade3_right_alternating (u v : V) :
    blade3 R V u v v = 0 := by
  dsimp [blade3]
  calc blade1 R V u * blade1 R V v * blade1 R V v
    _ = blade1 R V u * (blade1 R V v * blade1 R V v) := by simp [mul_assoc]
    _ = blade1 R V u * 0 := by rw [blade1_sq_zero R V v]
    _ = 0 := by simp

theorem blade3_swap_first_two (u v w : V) :
    blade3 R V u v w = - blade3 R V v u w := by
  dsimp [blade3]
  have h_swap : blade1 R V u * blade1 R V v = - (blade1 R V v * blade1 R V u) := blade1_swap_neg R V u v
  calc blade1 R V u * blade1 R V v * blade1 R V w
    _ = (blade1 R V u * blade1 R V v) * blade1 R V w := by simp [mul_assoc]
    _ = -(blade1 R V v * blade1 R V u) * blade1 R V w := by rw [h_swap]
    _ = -(blade1 R V v * blade1 R V u * blade1 R V w) := by simp [mul_assoc]

theorem blade3_swap_last_two (u v w : V) :
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

theorem blade2_mul_repeated_right_zero (u v : V) :
    blade2 R V u v * blade1 R V v = 0 := by
  dsimp [blade2]
  calc blade1 R V u * blade1 R V v * blade1 R V v
    _ = blade1 R V u * (blade1 R V v * blade1 R V v) := by simp [mul_assoc]
    _ = blade1 R V u * 0 := by rw [blade1_sq_zero R V v]
    _ = 0 := by simp

theorem blade2_mul_repeated_left_zero (u v : V) :
    blade1 R V u * blade2 R V u v = 0 := by
  dsimp [blade2]
  calc blade1 R V u * (blade1 R V u * blade1 R V v)
    _ = (blade1 R V u * blade1 R V u) * blade1 R V v := by simp [mul_assoc]
    _ = 0 * blade1 R V v := by rw [blade1_sq_zero R V u]
    _ = 0 := by simp

end InfoGeometry.SplitOctonions
