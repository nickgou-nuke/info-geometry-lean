import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Cuntz Algebra 𝒪₂: Canonical Endomorphism and Braid Twist
Strict formalization of the topological shift lifted to the operator algebra.
We prove that the canonical endomorphism Φ(X) = S₁XS₁* + S₂XS₂* is a 
strict *-homomorphism, encoding the fractal dynamics of the Cantor set.
We additionally construct the unitary Braid Twist, proving its symmetries.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CuntzEndomorphism

section CuntzEndomorphism

variable {A : Type*} [Ring A] [StarRing A]

/-- The fundamental relations of the Cuntz Algebra 𝒪₂. -/
class CuntzO2 (S₁ S₂ : A) : Prop where
  isom₁ : star S₁ * S₁ = 1
  isom₂ : star S₂ * S₂ = 1
  cuntz_sum : S₁ * star S₁ + S₂ * star S₂ = 1
  ortho₁₂ : star S₁ * S₂ = 0
  ortho₂₁ : star S₂ * S₁ = 0

variable (S₁ S₂ : A) [hC : CuntzO2 S₁ S₂]

/-- 
  The Canonical Shift Endomorphism Φ.
  This acts as the macroscopic scaling operator on the fractal vacuum.
-/
def CuntzShift (X : A) : A :=
  S₁ * X * star S₁ + S₂ * X * star S₂

/-- Φ preserves the identity (unital). -/
theorem CuntzShift_one : CuntzShift S₁ S₂ 1 = 1 := by
  dsimp [CuntzShift]
  rw [mul_one, mul_one]
  exact hC.cuntz_sum

/-- Φ preserves addition (linear). -/
theorem CuntzShift_add (X Y : A) : CuntzShift S₁ S₂ (X + Y) = CuntzShift S₁ S₂ X + CuntzShift S₁ S₂ Y := by
  dsimp [CuntzShift]
  calc S₁ * (X + Y) * star S₁ + S₂ * (X + Y) * star S₂
    _ = (S₁ * X + S₁ * Y) * star S₁ + (S₂ * X + S₂ * Y) * star S₂ := by rw [mul_add, mul_add]
    _ = S₁ * X * star S₁ + S₁ * Y * star S₁ + (S₂ * X * star S₂ + S₂ * Y * star S₂) := by rw [add_mul, add_mul]
    _ = S₁ * X * star S₁ + S₂ * X * star S₂ + (S₁ * Y * star S₁ + S₂ * Y * star S₂) := by ac_rfl

/-- Φ preserves multiplication (algebra homomorphism). -/
theorem CuntzShift_mul (X Y : A) : CuntzShift S₁ S₂ (X * Y) = CuntzShift S₁ S₂ X * CuntzShift S₁ S₂ Y := by
  dsimp [CuntzShift]
  have h1 : star S₁ * S₁ = 1 := hC.isom₁
  have h2 : star S₂ * S₂ = 1 := hC.isom₂
  have h12 : star S₁ * S₂ = 0 := hC.ortho₁₂
  have h21 : star S₂ * S₁ = 0 := hC.ortho₂₁

  have step1 : (S₁ * X * star S₁ + S₂ * X * star S₂) * (S₁ * Y * star S₁ + S₂ * Y * star S₂) = 
    (S₁ * X * star S₁) * (S₁ * Y * star S₁) + (S₁ * X * star S₁) * (S₂ * Y * star S₂) + 
    ((S₂ * X * star S₂) * (S₁ * Y * star S₁) + (S₂ * X * star S₂) * (S₂ * Y * star S₂)) := by 
    rw [add_mul, mul_add, mul_add]

  have t1 : (S₁ * X * star S₁) * (S₁ * Y * star S₁) = S₁ * (X * Y) * star S₁ := by
    calc (S₁ * X * star S₁) * (S₁ * Y * star S₁)
      _ = S₁ * X * (star S₁ * S₁) * Y * star S₁ := by simp only [mul_assoc]
      _ = S₁ * X * 1 * Y * star S₁ := by rw [h1]
      _ = S₁ * (X * Y) * star S₁ := by simp only [mul_one, mul_assoc]

  have t2 : (S₁ * X * star S₁) * (S₂ * Y * star S₂) = 0 := by
    calc (S₁ * X * star S₁) * (S₂ * Y * star S₂)
      _ = S₁ * X * (star S₁ * S₂) * Y * star S₂ := by simp only [mul_assoc]
      _ = S₁ * X * 0 * Y * star S₂ := by rw [h12]
      _ = 0 := by simp only [mul_zero, zero_mul]

  have t3 : (S₂ * X * star S₂) * (S₁ * Y * star S₁) = 0 := by
    calc (S₂ * X * star S₂) * (S₁ * Y * star S₁)
      _ = S₂ * X * (star S₂ * S₁) * Y * star S₁ := by simp only [mul_assoc]
      _ = S₂ * X * 0 * Y * star S₁ := by rw [h21]
      _ = 0 := by simp only [mul_zero, zero_mul]

  have t4 : (S₂ * X * star S₂) * (S₂ * Y * star S₂) = S₂ * (X * Y) * star S₂ := by
    calc (S₂ * X * star S₂) * (S₂ * Y * star S₂)
      _ = S₂ * X * (star S₂ * S₂) * Y * star S₂ := by simp only [mul_assoc]
      _ = S₂ * X * 1 * Y * star S₂ := by rw [h2]
      _ = S₂ * (X * Y) * star S₂ := by simp only [mul_one, mul_assoc]

  rw [step1, t1, t2, t3, t4]
  simp only [add_zero, zero_add]

/-- Φ preserves the star involution (*-homomorphism). -/
theorem CuntzShift_star (X : A) : CuntzShift S₁ S₂ (star X) = star (CuntzShift S₁ S₂ X) := by
  dsimp [CuntzShift]
  simp only [star_add, star_mul, star_star]
  ac_rfl

/-- 
  The Cuntz Braid Twist (Unitary Flip).
  Generates the symmetric permutation on the fractal Cantor branches, 
  forming the fundamental representation of the Braid Group.
-/
def BraidTwist : A := S₁ * star S₂ + S₂ * star S₁

/-- The Braid Twist is self-adjoint (an observable symmetry). -/
theorem BraidTwist_self_adjoint : star (BraidTwist S₁ S₂) = BraidTwist S₁ S₂ := by
  dsimp [BraidTwist]
  simp only [star_add, star_mul, star_star]
  exact add_comm _ _

/-- The Braid Twist is unitary (involutive), preserving probability. -/
theorem BraidTwist_unitary : BraidTwist S₁ S₂ * BraidTwist S₁ S₂ = 1 := by
  dsimp [BraidTwist]
  have h1 : star S₁ * S₁ = 1 := hC.isom₁
  have h2 : star S₂ * S₂ = 1 := hC.isom₂
  have h12 : star S₁ * S₂ = 0 := hC.ortho₁₂
  have h21 : star S₂ * S₁ = 0 := hC.ortho₂₁
  have hsum : S₁ * star S₁ + S₂ * star S₂ = 1 := hC.cuntz_sum

  have step1 : (S₁ * star S₂ + S₂ * star S₁) * (S₁ * star S₂ + S₂ * star S₁) =
    (S₁ * star S₂) * (S₁ * star S₂) + (S₁ * star S₂) * (S₂ * star S₁) +
    ((S₂ * star S₁) * (S₁ * star S₂) + (S₂ * star S₁) * (S₂ * star S₁)) := by
    rw [add_mul, mul_add, mul_add]

  have t1 : (S₁ * star S₂) * (S₁ * star S₂) = 0 := by
    calc (S₁ * star S₂) * (S₁ * star S₂)
      _ = S₁ * (star S₂ * S₁) * star S₂ := by simp only [mul_assoc]
      _ = S₁ * 0 * star S₂ := by rw [h21]
      _ = 0 := by simp only [mul_zero, zero_mul]

  have t2 : (S₁ * star S₂) * (S₂ * star S₁) = S₁ * star S₁ := by
    calc (S₁ * star S₂) * (S₂ * star S₁)
      _ = S₁ * (star S₂ * S₂) * star S₁ := by simp only [mul_assoc]
      _ = S₁ * 1 * star S₁ := by rw [h2]
      _ = S₁ * star S₁ := by simp only [mul_one]

  have t3 : (S₂ * star S₁) * (S₁ * star S₂) = S₂ * star S₂ := by
    calc (S₂ * star S₁) * (S₁ * star S₂)
      _ = S₂ * (star S₁ * S₁) * star S₂ := by simp only [mul_assoc]
      _ = S₂ * 1 * star S₂ := by rw [h1]
      _ = S₂ * star S₂ := by simp only [mul_one]

  have t4 : (S₂ * star S₁) * (S₂ * star S₁) = 0 := by
    calc (S₂ * star S₁) * (S₂ * star S₁)
      _ = S₂ * (star S₁ * S₂) * star S₁ := by simp only [mul_assoc]
      _ = S₂ * 0 * star S₁ := by rw [h12]
      _ = 0 := by simp only [mul_zero, zero_mul]

  rw [step1, t1, t2, t3, t4]
  simp only [zero_add, add_zero]
  exact hsum

end CuntzEndomorphism

end CuntzEndomorphism
