import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic

namespace InfoGeometry.GrassmannianTower

variable (R : Type*) [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

open ExteriorAlgebra

def blade_one (v : V) : ExteriorAlgebra R V := ι R v

theorem blade_one_sq_zero (k : V) :
    blade_one R k * blade_one R k = 0 :=
  ι_sq_zero k

lemma blade_one_anticomm (u v : V) :
    blade_one R u * blade_one R v + blade_one R v * blade_one R u = 0 := by
  dsimp [blade_one]
  have h_sq : ι R (u + v) * ι R (u + v) = 0 := ι_sq_zero (u + v)
  rw [map_add, add_mul, mul_add, mul_add] at h_sq
  rw [ι_sq_zero u, ι_sq_zero v] at h_sq
  simp only [zero_add, add_zero] at h_sq
  exact h_sq

lemma blade_one_swap_neg (u v : V) :
    blade_one R u * blade_one R v = - (blade_one R v * blade_one R u) := by
  have h := blade_one_anticomm R u v
  exact eq_neg_of_add_eq_zero_left h

def blade_two (u v : V) : ExteriorAlgebra R V :=
  blade_one R u * blade_one R v

theorem plucker_on_shell_condition (u v : V) :
    blade_two R u v * blade_two R u v = 0 := by
  dsimp [blade_two]
  have h1 : blade_one R u * blade_one R v * (blade_one R u * blade_one R v) =
      blade_one R u * (blade_one R v * blade_one R u) * blade_one R v := by
    simp only [mul_assoc]
  rw [h1]
  rw [blade_one_swap_neg R v u]
  have h2 : blade_one R u * -(blade_one R u * blade_one R v) * blade_one R v =
      - (blade_one R u * blade_one R u * (blade_one R v * blade_one R v)) := by
    simp only [mul_assoc, mul_neg, neg_mul]
  rw [h2]
  rw [blade_one_sq_zero R u]
  simp

def blade_three (u v w : V) : ExteriorAlgebra R V :=
  blade_one R u * blade_one R v * blade_one R w

theorem associator_left_alt (u v : V) :
    blade_three R u u v = 0 := by
  dsimp [blade_three]
  have h : blade_one R u * blade_one R u * blade_one R v =
      (blade_one R u * blade_one R u) * blade_one R v := by simp only [mul_assoc]
  rw [h, blade_one_sq_zero R u, zero_mul]

theorem associator_right_alt (u v : V) :
    blade_three R u v v = 0 := by
  dsimp [blade_three]
  rw [mul_assoc, blade_one_sq_zero R v, mul_zero]

theorem associator_swap_12 (u v w : V) :
    blade_three R u v w = - blade_three R v u w := by
  dsimp [blade_three]
  have h : blade_one R u * blade_one R v * blade_one R w =
      (blade_one R u * blade_one R v) * blade_one R w := by simp only [mul_assoc]
  rw [h, blade_one_swap_neg R u v, neg_mul]

def blade_four (u v w z : V) : ExteriorAlgebra R V :=
  blade_three R u v w * blade_one R z

theorem topological_volume_collapse (u v w : V) :
    blade_four R u v w w = 0 := by
  dsimp [blade_four, blade_three]
  have h : blade_one R u * blade_one R v * blade_one R w * blade_one R w =
      (blade_one R u * blade_one R v) * (blade_one R w * blade_one R w) := by simp only [mul_assoc]
  rw [h, blade_one_sq_zero R w, mul_zero]

end InfoGeometry.GrassmannianTower
