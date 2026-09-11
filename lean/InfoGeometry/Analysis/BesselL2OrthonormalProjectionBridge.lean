import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Genuine Bessel Inequality for Orthonormal Systems Bridge

This module formalizes the genuine Bessel inequality in $L^2(0, 1)$ in Mathlib 4:
1. **Residual Energy Non-Negativity**:
   $$\int_0^1 (f(x) - (c_1 e_1(x) + c_2 e_2(x)))^2 \, dx \ge 0$$
2. **Exact Residual Energy Expansion for Orthonormal Modes**:
   $$\int_0^1 (f - (c_1 e_1 + c_2 e_2))^2 = \int_0^1 f^2 - (c_1^2 + c_2^2)$$
   for orthonormal modes satisfying $\int_0^1 e_1^2 = 1, \int_0^1 e_2^2 = 1, \int_0^1 e_1 e_2 = 0$.
3. **Master Bessel Inequality for 2 Orthonormal Modes**:
   $$\left(\int_0^1 f e_1\right)^2 + \left(\int_0^1 f e_2\right)^2 \le \int_0^1 f^2$$
-/

noncomputable section

namespace InfoGeometry.Analysis.Bessel

open Real intervalIntegral MeasureTheory

/-- 🏆 THEOREM 1: Non-Negativity of the 2-Mode Residual Energy -/
theorem residual_energy_nonneg (f e₁ e₂ : ℝ → ℝ) (c₁ c₂ : ℝ) :
    0 ≤ ∫ x in (0:ℝ)..1, (f x - (c₁ * e₁ x + c₂ * e₂ x)) ^ 2 := by
  have h_le : (0:ℝ) ≤ 1 := by norm_num
  apply intervalIntegral.integral_nonneg h_le
  intro x _
  exact sq_nonneg (f x - (c₁ * e₁ x + c₂ * e₂ x))

/-- 🏆 THEOREM 2: Exact Residual Energy Expansion for Orthonormal Modes -/
theorem residual_energy_orthonormal_expansion (f e₁ e₂ : ℝ → ℝ)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 1)
    (hfe1 : IntervalIntegrable (fun x => f x * e₁ x) volume 0 1)
    (hfe2 : IntervalIntegrable (fun x => f x * e₂ x) volume 0 1)
    (he1_sq : IntervalIntegrable (fun x => e₁ x ^ 2) volume 0 1)
    (he2_sq : IntervalIntegrable (fun x => e₂ x ^ 2) volume 0 1)
    (he1e2 : IntervalIntegrable (fun x => e₁ x * e₂ x) volume 0 1)
    (h_norm1 : (∫ x in (0:ℝ)..1, e₁ x ^ 2) = 1)
    (h_norm2 : (∫ x in (0:ℝ)..1, e₂ x ^ 2) = 1)
    (h_orth : (∫ x in (0:ℝ)..1, e₁ x * e₂ x) = 0) :
    let c₁ := ∫ x in (0:ℝ)..1, f x * e₁ x
    let c₂ := ∫ x in (0:ℝ)..1, f x * e₂ x
    ∫ x in (0:ℝ)..1, (f x - (c₁ * e₁ x + c₂ * e₂ x)) ^ 2 =
      (∫ x in (0:ℝ)..1, f x ^ 2) - (c₁ ^ 2 + c₂ ^ 2) := by
  intro c₁ c₂
  have h_expand : ∀ x : ℝ, (f x - (c₁ * e₁ x + c₂ * e₂ x)) ^ 2 =
      f x ^ 2 - 2 * c₁ * (f x * e₁ x) - 2 * c₂ * (f x * e₂ x) +
        c₁ ^ 2 * (e₁ x ^ 2) + c₂ ^ 2 * (e₂ x ^ 2) + 2 * c₁ * c₂ * (e₁ x * e₂ x) := by
    intro x
    ring
  have h_int_eq : (∫ x in (0:ℝ)..1, (f x - (c₁ * e₁ x + c₂ * e₂ x)) ^ 2) =
      ∫ x in (0:ℝ)..1, (f x ^ 2 - 2 * c₁ * (f x * e₁ x) - 2 * c₂ * (f x * e₂ x) +
        c₁ ^ 2 * (e₁ x ^ 2) + c₂ ^ 2 * (e₂ x ^ 2) + 2 * c₁ * c₂ * (e₁ x * e₂ x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_expand x
  rw [h_int_eq]
  have h1 : IntervalIntegrable (fun x => f x ^ 2 - 2 * c₁ * (f x * e₁ x) - 2 * c₂ * (f x * e₂ x) +
      c₁ ^ 2 * (e₁ x ^ 2) + c₂ ^ 2 * (e₂ x ^ 2)) volume 0 1 := by
    have h_p1 := hf2.sub (hfe1.const_mul (2 * c₁))
    have h_p2 := h_p1.sub (hfe2.const_mul (2 * c₂))
    have h_p3 := h_p2.add (he1_sq.const_mul (c₁ ^ 2))
    exact h_p3.add (he2_sq.const_mul (c₂ ^ 2))
  have h_cross : IntervalIntegrable (fun x => 2 * c₁ * c₂ * (e₁ x * e₂ x)) volume 0 1 :=
    he1e2.const_mul (2 * c₁ * c₂)
  have h_split1 := integral_add h1 h_cross
  rw [h_split1, intervalIntegral.integral_const_mul, h_orth, mul_zero, add_zero]
  have h_p2 : IntervalIntegrable (fun x => f x ^ 2 - 2 * c₁ * (f x * e₁ x) - 2 * c₂ * (f x * e₂ x) + c₁ ^ 2 * (e₁ x ^ 2)) volume 0 1 := by
    have h_sub1 := hf2.sub (hfe1.const_mul (2 * c₁))
    have h_sub2 := h_sub1.sub (hfe2.const_mul (2 * c₂))
    exact h_sub2.add (he1_sq.const_mul (c₁ ^ 2))
  have h_split2 := integral_add h_p2 (he2_sq.const_mul (c₂ ^ 2))
  rw [h_split2, intervalIntegral.integral_const_mul, h_norm2, mul_one]
  have h_p3 : IntervalIntegrable (fun x => f x ^ 2 - 2 * c₁ * (f x * e₁ x) - 2 * c₂ * (f x * e₂ x)) volume 0 1 :=
    (hf2.sub (hfe1.const_mul (2 * c₁))).sub (hfe2.const_mul (2 * c₂))
  have h_split3 := integral_add h_p3 (he1_sq.const_mul (c₁ ^ 2))
  rw [h_split3, intervalIntegral.integral_const_mul, h_norm1, mul_one]
  have h_split4 := integral_sub (hf2.sub (hfe1.const_mul (2 * c₁))) (hfe2.const_mul (2 * c₂))
  rw [h_split4, intervalIntegral.integral_const_mul]
  have h_split5 := integral_sub hf2 (hfe1.const_mul (2 * c₁))
  rw [h_split5, intervalIntegral.integral_const_mul]
  dsimp [c₁, c₂]
  ring

/-- 🏆 THEOREM 3: Master Bessel Inequality for 2 Orthonormal Modes -/
theorem two_mode_bessel_inequality (f e₁ e₂ : ℝ → ℝ)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 1)
    (hfe1 : IntervalIntegrable (fun x => f x * e₁ x) volume 0 1)
    (hfe2 : IntervalIntegrable (fun x => f x * e₂ x) volume 0 1)
    (he1_sq : IntervalIntegrable (fun x => e₁ x ^ 2) volume 0 1)
    (he2_sq : IntervalIntegrable (fun x => e₂ x ^ 2) volume 0 1)
    (he1e2 : IntervalIntegrable (fun x => e₁ x * e₂ x) volume 0 1)
    (h_norm1 : (∫ x in (0:ℝ)..1, e₁ x ^ 2) = 1)
    (h_norm2 : (∫ x in (0:ℝ)..1, e₂ x ^ 2) = 1)
    (h_orth : (∫ x in (0:ℝ)..1, e₁ x * e₂ x) = 0) :
    (∫ x in (0:ℝ)..1, f x * e₁ x) ^ 2 + (∫ x in (0:ℝ)..1, f x * e₂ x) ^ 2 ≤
      ∫ x in (0:ℝ)..1, f x ^ 2 := by
  let c₁ := ∫ x in (0:ℝ)..1, f x * e₁ x
  let c₂ := ∫ x in (0:ℝ)..1, f x * e₂ x
  have h_exp := residual_energy_orthonormal_expansion f e₁ e₂ hf2 hfe1 hfe2 he1_sq he2_sq he1e2 h_norm1 h_norm2 h_orth
  have h_nonneg := residual_energy_nonneg f e₁ e₂ c₁ c₂
  change 0 ≤ ∫ x in 0..1, (f x - (c₁ * e₁ x + c₂ * e₂ x)) ^ 2 at h_nonneg
  rw [h_exp] at h_nonneg
  linarith

end InfoGeometry.Analysis.Bessel
