import Mathlib.Algebra.Star.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic

/-!
# Cuntz Algebra 𝒪₂ and Cantor Space Isometries
Strict formalization of the Cuntz superalgebra representations, 
orthogonality of generators, and their actions on infinite binary qubit words.
-/

section CuntzAlgebra

variable {A : Type*} [Ring A] [StarRing A]

/-- The fundamental relations of the Cuntz Algebra 𝒪₂. -/
class CuntzO2 (S₁ S₂ : A) : Prop where
  isom₁ : star S₁ * S₁ = 1
  isom₂ : star S₂ * S₂ = 1
  cuntz_sum : S₁ * star S₁ + S₂ * star S₂ = 1

/-- 
  Strict algebraic proof that the Cuntz isometries are mutually orthogonal.
  S₁* S₂ = 0 natively derived from the Cuntz sum and isometry conditions.
-/
theorem cuntz_ortho_12 (S₁ S₂ : A) [hC : CuntzO2 S₁ S₂] : star S₁ * S₂ = 0 := by
  have h1 : star S₁ * S₁ = 1 := hC.isom₁
  have h2 : star S₂ * S₂ = 1 := hC.isom₂
  have h3 : S₁ * star S₁ + S₂ * star S₂ = 1 := hC.cuntz_sum
  
  have step1 : star S₁ * (S₁ * star S₁ + S₂ * star S₂) * S₂ = star S₁ * 1 * S₂ := by rw [h3]
  
  have step2 : star S₁ * (S₁ * star S₁ + S₂ * star S₂) * S₂ = star S₁ * S₂ + star S₁ * S₂ := by
    calc star S₁ * (S₁ * star S₁ + S₂ * star S₂) * S₂
      _ = (star S₁ * (S₁ * star S₁) + star S₁ * (S₂ * star S₂)) * S₂ := by rw [mul_add]
      _ = ((star S₁ * S₁) * star S₁ + star S₁ * S₂ * star S₂) * S₂ := by simp only [←mul_assoc]
      _ = (1 * star S₁ + star S₁ * S₂ * star S₂) * S₂ := by rw [h1]
      _ = (star S₁ + star S₁ * S₂ * star S₂) * S₂ := by rw [one_mul]
      _ = star S₁ * S₂ + (star S₁ * S₂ * star S₂) * S₂ := by rw [add_mul]
      _ = star S₁ * S₂ + star S₁ * S₂ * (star S₂ * S₂) := by simp only [mul_assoc]
      _ = star S₁ * S₂ + star S₁ * S₂ * 1 := by rw [h2]
      _ = star S₁ * S₂ + star S₁ * S₂ := by rw [mul_one]
      
  rw [mul_one] at step1
  rw [step2] at step1
  
  calc star S₁ * S₂
    _ = (star S₁ * S₂ + star S₁ * S₂) - star S₁ * S₂ := by rw [add_sub_cancel_right]
    _ = star S₁ * S₂ - star S₁ * S₂ := by rw [step1]
    _ = 0 := sub_self _

theorem cuntz_ortho_21 (S₁ S₂ : A) [hC : CuntzO2 S₁ S₂] : star S₂ * S₁ = 0 := by
  have h1 : star S₁ * S₁ = 1 := hC.isom₁
  have h2 : star S₂ * S₂ = 1 := hC.isom₂
  have h3 : S₁ * star S₁ + S₂ * star S₂ = 1 := hC.cuntz_sum
  
  have step1 : star S₂ * (S₁ * star S₁ + S₂ * star S₂) * S₁ = star S₂ * 1 * S₁ := by rw [h3]
  
  have step2 : star S₂ * (S₁ * star S₁ + S₂ * star S₂) * S₁ = star S₂ * S₁ + star S₂ * S₁ := by
    calc star S₂ * (S₁ * star S₁ + S₂ * star S₂) * S₁
      _ = (star S₂ * (S₁ * star S₁) + star S₂ * (S₂ * star S₂)) * S₁ := by rw [mul_add]
      _ = (star S₂ * S₁ * star S₁ + (star S₂ * S₂) * star S₂) * S₁ := by simp only [←mul_assoc]
      _ = (star S₂ * S₁ * star S₁ + 1 * star S₂) * S₁ := by rw [h2]
      _ = (star S₂ * S₁ * star S₁ + star S₂) * S₁ := by rw [one_mul]
      _ = (star S₂ * S₁ * star S₁) * S₁ + star S₂ * S₁ := by rw [add_mul]
      _ = star S₂ * S₁ * (star S₁ * S₁) + star S₂ * S₁ := by simp only [mul_assoc]
      _ = star S₂ * S₁ * 1 + star S₂ * S₁ := by rw [h1]
      _ = star S₂ * S₁ + star S₂ * S₁ := by rw [mul_one]

  rw [mul_one] at step1
  rw [step2] at step1

  calc star S₂ * S₁
    _ = (star S₂ * S₁ + star S₂ * S₁) - star S₂ * S₁ := by rw [add_sub_cancel_right]
    _ = star S₂ * S₁ - star S₂ * S₁ := by rw [step1]
    _ = 0 := sub_self _

end CuntzAlgebra

/-!
# Cantor Set Dynamics
Infinite binary qubit words represented via functions from ℕ → Bool.
-/

section CantorSpace

/-- The Cantor set of infinite binary words. -/
def Cantor := ℕ → Bool

/-- The left Cuntz isometry S₁: injects 0 (false) at the root. -/
def S1_action (x : Cantor) : Cantor
  | 0 => false
  | n + 1 => x n

/-- The right Cuntz isometry S₂: injects 1 (true) at the root. -/
def S2_action (x : Cantor) : Cantor
  | 0 => true
  | n + 1 => x n

/-- The topological shift operator: acts as the left inverse (annihilator). -/
def shift (x : Cantor) : Cantor := fun n => x (n + 1)

/-- Formal proof that the shift operator perfectly annihilates the S₁ injection. -/
theorem shift_S1_eq_id (x : Cantor) : shift (S1_action x) = x := by
  funext n
  rfl

/-- Formal proof that the shift operator perfectly annihilates the S₂ injection. -/
theorem shift_S2_eq_id (x : Cantor) : shift (S2_action x) = x := by
  funext n
  rfl

/-- Disjointness of the topological ranges of S₁ and S₂ on the Cantor set. -/
theorem S1_neq_S2 (x y : Cantor) : S1_action x ≠ S2_action y := by
  intro h
  have h0 : S1_action x 0 = S2_action y 0 := congrFun h 0
  contradiction

end CantorSpace
