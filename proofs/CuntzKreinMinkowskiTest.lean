import Mathlib

structure CuntzO2 (A : Type*) [Ring A] [StarRing A] where
  S₁ : A
  S₂ : A
  isometry₁ : star S₁ * S₁ = 1
  isometry₂ : star S₂ * S₂ = 1
  completeness : S₁ * star S₁ + S₂ * star S₂ = 1

namespace CuntzO2

variable {A : Type*} [Ring A] [StarRing A] (O : CuntzO2 A)

theorem ortho_S₁_star_S₂ : star O.S₁ * O.S₂ = 0 := by
  have h1 : star O.S₁ * (O.S₁ * star O.S₁ + O.S₂ * star O.S₂) * O.S₂ = star O.S₁ * 1 * O.S₂ := by
    rw [O.completeness]
  have h2 : star O.S₁ * (O.S₁ * star O.S₁ + O.S₂ * star O.S₂) * O.S₂ = star O.S₁ * O.S₂ + star O.S₁ * O.S₂ := by
    calc
      star O.S₁ * (O.S₁ * star O.S₁ + O.S₂ * star O.S₂) * O.S₂
        = (star O.S₁ * (O.S₁ * star O.S₁) + star O.S₁ * (O.S₂ * star O.S₂)) * O.S₂ := by rw [mul_add]
      _ = star O.S₁ * (O.S₁ * star O.S₁) * O.S₂ + star O.S₁ * (O.S₂ * star O.S₂) * O.S₂ := by rw [add_mul]
      _ = (star O.S₁ * O.S₁) * star O.S₁ * O.S₂ + star O.S₁ * O.S₂ * (star O.S₂ * O.S₂) := by simp only [mul_assoc]
      _ = 1 * star O.S₁ * O.S₂ + star O.S₁ * O.S₂ * 1 := by rw [O.isometry₁, O.isometry₂]
      _ = star O.S₁ * O.S₂ + star O.S₁ * O.S₂ := by simp only [one_mul, mul_one]
  have h3 : star O.S₁ * 1 * O.S₂ = star O.S₁ * O.S₂ := by simp only [mul_one]
  have h4 : star O.S₁ * O.S₂ + star O.S₁ * O.S₂ = star O.S₁ * O.S₂ := by
    rw [← h2, h1, h3]
  calc
    star O.S₁ * O.S₂ = star O.S₁ * O.S₂ + star O.S₁ * O.S₂ - star O.S₁ * O.S₂ := by simp only [add_sub_cancel_right]
    _ = star O.S₁ * O.S₂ - star O.S₁ * O.S₂ := by rw [h4]
    _ = 0 := by simp only [sub_self]

theorem ortho_S₂_star_S₁ : star O.S₂ * O.S₁ = 0 := by
  have h : star (star O.S₁ * O.S₂) = 0 := by rw [ortho_S₁_star_S₂ O, star_zero]
  calc
    star O.S₂ * O.S₁ = star O.S₂ * star (star O.S₁) := by simp only [star_star]
    _ = star (star O.S₁ * O.S₂) := by rw [star_mul]
    _ = 0 := h

def eta : A :=
  O.S₁ * star O.S₁ - O.S₂ * star O.S₂

theorem eta_self_adjoint : star (O.eta) = O.eta := by
  unfold eta
  simp only [star_sub, star_mul, star_star]

theorem eta_involution : O.eta * O.eta = 1 := by
  unfold eta
  have h12 : star O.S₁ * O.S₂ = 0 := ortho_S₁_star_S₂ O
  have h21 : star O.S₂ * O.S₁ = 0 := ortho_S₂_star_S₁ O
  have h1 : O.S₁ * star O.S₁ * (O.S₁ * star O.S₁) = O.S₁ * star O.S₁ := by
    rw [mul_assoc, ← mul_assoc (star O.S₁), O.S₁_isometry, one_mul]
  have h2 : O.S₁ * star O.S₁ * (O.S₂ * star O.S₂) = 0 := by
    rw [mul_assoc, ← mul_assoc (star O.S₁), h12, zero_mul, mul_zero]
  have h3 : O.S₂ * star O.S₂ * (O.S₁ * star O.S₁) = 0 := by
    rw [mul_assoc, ← mul_assoc (star O.S₂), h21, zero_mul, mul_zero]
  have h4 : O.S₂ * star O.S₂ * (O.S₂ * star O.S₂) = O.S₂ * star O.S₂ := by
    rw [mul_assoc, ← mul_assoc (star O.S₂), O.S₂_isometry, one_mul]
  simp only [sub_mul, mul_sub]
  rw [h1, h2, h3, h4]
  simp only [sub_zero, zero_sub, sub_neg_eq_add]
  exact O.cuntz_relation

end CuntzO2
