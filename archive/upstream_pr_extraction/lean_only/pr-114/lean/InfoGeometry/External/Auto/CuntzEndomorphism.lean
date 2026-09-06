import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace InfoGeometry.External.Auto.CuntzEndomorphism

section CuntzEndomorphism

variable {A : Type*} [Ring A] [StarRing A]

class CuntzO2 (S₁ S₂ : A) : Prop where
  isom₁ : star S₁ * S₁ = 1
  isom₂ : star S₂ * S₂ = 1
  cuntz_sum : S₁ * star S₁ + S₂ * star S₂ = 1
  ortho₁₂ : star S₁ * S₂ = 0
  ortho₂₁ : star S₂ * S₁ = 0

variable (S₁ S₂ : A) [hC : CuntzO2 S₁ S₂]

def CuntzShift (X : A) : A :=
  S₁ * X * star S₁ + S₂ * X * star S₂

theorem CuntzShift_one : CuntzShift S₁ S₂ 1 = 1 := by
  dsimp [CuntzShift]
  rw [mul_one, mul_one]
  simpa using hC.cuntz_sum

theorem CuntzShift_add (X Y : A) :
    CuntzShift S₁ S₂ (X + Y) = CuntzShift S₁ S₂ X + CuntzShift S₁ S₂ Y := by
  dsimp [CuntzShift]
  rw [mul_add, mul_add, add_mul, add_mul]
  ac_rfl

theorem CuntzShift_mul (X Y : A) :
    CuntzShift S₁ S₂ (X * Y) = CuntzShift S₁ S₂ X * CuntzShift S₁ S₂ Y := by
  dsimp [CuntzShift]
  rw [add_mul, mul_add, mul_add]
  have h1 := hC.isom₁
  have h2 := hC.isom₂
  have h12 := hC.ortho₁₂
  have h21 := hC.ortho₂₁
  have t11 : (S₁ * X * star S₁) * (S₁ * Y * star S₁) =
      S₁ * (X * Y) * star S₁ := by
    rw [show (S₁ * X * star S₁) * (S₁ * Y * star S₁) =
      S₁ * X * (star S₁ * S₁) * Y * star S₁ by simp only [mul_assoc], h1]
    simp only [mul_one, mul_assoc]
  have t12 : (S₁ * X * star S₁) * (S₂ * Y * star S₂) = 0 := by
    rw [show (S₁ * X * star S₁) * (S₂ * Y * star S₂) =
      S₁ * X * (star S₁ * S₂) * Y * star S₂ by simp only [mul_assoc], h12]
    simp
  have t21 : (S₂ * X * star S₂) * (S₁ * Y * star S₁) = 0 := by
    rw [show (S₂ * X * star S₂) * (S₁ * Y * star S₁) =
      S₂ * X * (star S₂ * S₁) * Y * star S₁ by simp only [mul_assoc], h21]
    simp
  have t22 : (S₂ * X * star S₂) * (S₂ * Y * star S₂) =
      S₂ * (X * Y) * star S₂ := by
    rw [show (S₂ * X * star S₂) * (S₂ * Y * star S₂) =
      S₂ * X * (star S₂ * S₂) * Y * star S₂ by simp only [mul_assoc], h2]
    simp only [mul_one, mul_assoc]
  rw [t11, t12, t21, t22]
  simp

theorem CuntzShift_star (X : A) :
    CuntzShift S₁ S₂ (star X) = star (CuntzShift S₁ S₂ X) := by
  dsimp [CuntzShift]
  simp only [star_add, star_mul, star_star]
  ac_rfl

def BraidTwist : A := S₁ * star S₂ + S₂ * star S₁

theorem BraidTwist_self_adjoint : star (BraidTwist S₁ S₂) = BraidTwist S₁ S₂ := by
  dsimp [BraidTwist]
  simp only [star_add, star_mul, star_star]
  ac_rfl

theorem BraidTwist_unitary : BraidTwist S₁ S₂ * BraidTwist S₁ S₂ = 1 := by
  dsimp [BraidTwist]
  rw [add_mul, mul_add, mul_add]
  have h1 := hC.isom₁
  have h2 := hC.isom₂
  have h12 := hC.ortho₁₂
  have h21 := hC.ortho₂₁
  rw [show (S₁ * star S₂) * (S₁ * star S₂) = 0 by
        rw [show (S₁ * star S₂) * (S₁ * star S₂) =
          S₁ * (star S₂ * S₁) * star S₂ by simp only [mul_assoc], h21]; simp,
      show (S₁ * star S₂) * (S₂ * star S₁) = S₁ * star S₁ by
        rw [show (S₁ * star S₂) * (S₂ * star S₁) =
          S₁ * (star S₂ * S₂) * star S₁ by simp only [mul_assoc], h2]; simp,
      show (S₂ * star S₁) * (S₁ * star S₂) = S₂ * star S₂ by
        rw [show (S₂ * star S₁) * (S₁ * star S₂) =
          S₂ * (star S₁ * S₁) * star S₂ by simp only [mul_assoc], h1]; simp,
      show (S₂ * star S₁) * (S₂ * star S₁) = 0 by
        rw [show (S₂ * star S₁) * (S₂ * star S₁) =
          S₂ * (star S₁ * S₂) * star S₁ by simp only [mul_assoc], h12]; simp]
  simpa using hC.cuntz_sum

end CuntzEndomorphism

end InfoGeometry.External.Auto.CuntzEndomorphism
