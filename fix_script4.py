content = """import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.SplitOctonions

variable (R : Type*) [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

open ExteriorAlgebra

/-! ### 1. Split-Signature Metric and the Isotropic Null Cone -/

def IsIsotropic (Q : QuadraticForm R V) (v : V) : Prop :=
  Q v = 0

def IsotropicCone (Q : QuadraticForm R V) : Set V :=
  {v : V | IsIsotropic R Q v}

/-! ### 2. The Universal Graded Commutator on Exterior Blades -/

def gradedSign (degA degB : ℕ) : R :=
  if (degA * degB) % 2 = 1 then -1 else 1

def gradedBracket (degA degB : ℕ) (A B : ExteriorAlgebra R V) : ExteriorAlgebra R V :=
  A * B - gradedSign R degA degB • (B * A)

/-! ### 3. Grade 1: Odd Vectors, Anticommutation, and Massless Lightcones -/

def blade1 (v : V) : ExteriorAlgebra R V :=
  ι R v

lemma gradedSign_one_one : (gradedSign R 1 1) = -1 := by
  dsimp [gradedSign]

theorem gradedBracket_grade1 (u v : V) :
    gradedBracket R 1 1 (blade1 R u) (blade1 R v) = blade1 R u * blade1 R v + blade1 R v * blade1 R u := by
  dsimp [gradedBracket]
  rw [gradedSign_one_one R]
  simp only [neg_smul, one_smul, sub_neg_eq_add]

theorem blade1_sq_zero (k : V) :
    blade1 R k * blade1 R k = 0 :=
  ι_sq_zero k

theorem blade1_gradedBracket_self_zero (u v : V) :
    gradedBracket R 1 1 (blade1 R u) (blade1 R v) = 0 := by
  rw [gradedBracket_grade1 R]
  unfold blade1
  have h_sq : ι R (u + v) * ι R (u + v) = 0 := ι_sq_zero (u + v)
  rw [map_add, add_mul, mul_add, mul_add] at h_sq
  rw [ι_sq_zero u, ι_sq_zero v] at h_sq
  simp only [zero_add, add_zero] at h_sq
  exact h_sq

lemma blade1_swap_neg (u v : V) :
    blade1 R u * blade1 R v = - (blade1 R v * blade1 R u) := by
  have h := blade1_gradedBracket_self_zero R u v
  rw [gradedBracket_grade1 R] at h
  exact eq_neg_of_add_eq_zero_left h

/-! ### 4. Grade 2: Even Bivectors and the Klein Quadric -/

def blade2 (u v : V) : ExteriorAlgebra R V :=
  blade1 R u * blade1 R v

lemma gradedSign_two_two : (gradedSign R 2 2) = 1 := by
  dsimp [gradedSign]

theorem gradedBracket_grade2 (P Q : ExteriorAlgebra R V) :
    gradedBracket R 2 2 P Q = P * Q - Q * P := by
  dsimp [gradedBracket]
  rw [gradedSign_two_two R]
  simp only [one_smul]

lemma blade1_mul_blade1_mul (u : V) (X : ExteriorAlgebra R V) :
    blade1 R u * (blade1 R u * X) = 0 := by
  rw [← mul_assoc, blade1_sq_zero R u, zero_mul]

theorem plucker_on_shell_quadric (u v : V) :
    blade2 R u v * blade2 R u v = 0 := by
  unfold blade2
  have h1 : blade1 R u * blade1 R v * (blade1 R u * blade1 R v) = blade1 R u * (blade1 R v * (blade1 R u * blade1 R v)) := by simp only [mul_assoc]
  have h2 : blade1 R v * (blade1 R u * blade1 R v) = (blade1 R v * blade1 R u) * blade1 R v := by simp only [mul_assoc]
  rw [h1, h2, blade1_swap_neg R v u]
  simp only [neg_mul, mul_neg, mul_assoc]
  rw [blade1_mul_blade1_mul R u]
  simp only [neg_zero]

/-! ### 5. Grade 3: The Split-Octonionic Associator Defect (R-Flux) -/

def blade3 (u v w : V) : ExteriorAlgebra R V :=
  blade1 R u * blade1 R v * blade1 R w

theorem associator_left_alternating (u v : V) :
    blade3 R u u v = 0 := by
  unfold blade3
  rw [← mul_assoc, blade1_sq_zero R u, zero_mul]

theorem associator_right_alternating (u v : V) :
    blade3 R u v v = 0 := by
  unfold blade3
  rw [mul_assoc, blade1_sq_zero R v, mul_zero]

theorem associator_swap_adjacent (u v w : V) :
    blade3 R u v w = - blade3 R v u w := by
  unfold blade3
  rw [← mul_assoc, blade1_swap_neg R u v, neg_mul]

theorem associator_swap_cyclic (u v w : V) :
    blade3 R u v w = - blade3 R u w v := by
  unfold blade3
  rw [mul_assoc, blade1_swap_neg R v w, mul_neg]

/-! ### 6. The 5-Graded Cartan Truncation -/

theorem gradedBracket_grade1_grade2 (v : V) (P : ExteriorAlgebra R V) :
    gradedBracket R 1 2 (blade1 R v) P = blade1 R v * P - P * blade1 R v := by
  dsimp [gradedBracket, gradedSign]
  simp only [one_smul]

theorem kkt_truncation_right (u v : V) :
    blade2 R u v * blade1 R v = 0 := by
  unfold blade2
  rw [mul_assoc, blade1_sq_zero R v, mul_zero]

theorem kkt_truncation_left (u v : V) :
    blade1 R u * blade2 R u v = 0 := by
  unfold blade2
  rw [← mul_assoc, blade1_sq_zero R u, zero_mul]

end InfoGeometry.SplitOctonions
"""
with open("lean/InfoGeometry/SplitOctonions/GradedBlades.lean", "w") as f:
    f.write(content)
