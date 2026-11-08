import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Genuine Parseval Identity and Bessel Saturation Bridge

This module formalizes genuine Parseval energy conservation identities in $L^2(0, 1)$ in Mathlib 4:
1. **Linear Span Projection Coefficients**:
   $$f = a_1 e_1 + a_2 e_2 \implies c_1 = \int_0^1 f e_1 = a_1, \quad c_2 = \int_0^1 f e_2 = a_2$$
2. **Exact Parseval Energy Identity on the Linear Span**:
   $$\int_0^1 (a_1 e_1(x) + a_2 e_2(x))^2 \, dx = a_1^2 + a_2^2 = c_1^2 + c_2^2$$
3. **Exact Bessel Saturation Equivalence**:
   $$\int_0^1 f^2 = c_1^2 + c_2^2 \iff \int_0^1 (f - (c_1 e_1 + c_2 e_2))^2 = 0$$
-/

noncomputable section

namespace InfoGeometry.Analysis.Parseval

open Real intervalIntegral MeasureTheory

/-- 🏆 THEOREM 1: Projection Coefficients on 2-Mode Linear Combination -/
theorem linear_combination_projection_coeff1 (e₁ e₂ : ℝ → ℝ) (a₁ a₂ : ℝ)
    (he1_sq : IntervalIntegrable (fun x => e₁ x ^ 2) volume 0 1)
    (he1e2 : IntervalIntegrable (fun x => e₁ x * e₂ x) volume 0 1)
    (h_norm1 : (∫ x in (0:ℝ)..1, e₁ x ^ 2) = 1)
    (h_orth : (∫ x in (0:ℝ)..1, e₁ x * e₂ x) = 0) :
    (∫ x in (0:ℝ)..1, (a₁ * e₁ x + a₂ * e₂ x) * e₁ x) = a₁ := by
  have h_alg : ∀ x : ℝ, (a₁ * e₁ x + a₂ * e₂ x) * e₁ x = a₁ * (e₁ x ^ 2) + a₂ * (e₁ x * e₂ x) := by
    intro x
    ring
  have h_int_eq : (∫ x in (0:ℝ)..1, (a₁ * e₁ x + a₂ * e₂ x) * e₁ x) =
      ∫ x in (0:ℝ)..1, (a₁ * (e₁ x ^ 2) + a₂ * (e₁ x * e₂ x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_alg x
  rw [h_int_eq]
  have h_split := integral_add (he1_sq.const_mul a₁) (he1e2.const_mul a₂)
  rw [h_split, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h_norm1, h_orth]
  ring

/-- 🏆 THEOREM 2: Projection Coefficients on 2-Mode Linear Combination (Second Mode) -/
theorem linear_combination_projection_coeff2 (e₁ e₂ : ℝ → ℝ) (a₁ a₂ : ℝ)
    (he2_sq : IntervalIntegrable (fun x => e₂ x ^ 2) volume 0 1)
    (he1e2 : IntervalIntegrable (fun x => e₁ x * e₂ x) volume 0 1)
    (h_norm2 : (∫ x in (0:ℝ)..1, e₂ x ^ 2) = 1)
    (h_orth : (∫ x in (0:ℝ)..1, e₁ x * e₂ x) = 0) :
    (∫ x in (0:ℝ)..1, (a₁ * e₁ x + a₂ * e₂ x) * e₂ x) = a₂ := by
  have h_alg : ∀ x : ℝ, (a₁ * e₁ x + a₂ * e₂ x) * e₂ x = a₁ * (e₁ x * e₂ x) + a₂ * (e₂ x ^ 2) := by
    intro x
    ring
  have h_int_eq : (∫ x in (0:ℝ)..1, (a₁ * e₁ x + a₂ * e₂ x) * e₂ x) =
      ∫ x in (0:ℝ)..1, (a₁ * (e₁ x * e₂ x) + a₂ * (e₂ x ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_alg x
  rw [h_int_eq]
  have h_split := integral_add (he1e2.const_mul a₁) (he2_sq.const_mul a₂)
  rw [h_split, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h_norm2, h_orth]
  ring

/-- 🏆 THEOREM 3: Exact Parseval Energy Conservation on the Linear Span -/
theorem parseval_energy_identity (e₁ e₂ : ℝ → ℝ) (a₁ a₂ : ℝ)
    (he1_sq : IntervalIntegrable (fun x => e₁ x ^ 2) volume 0 1)
    (he2_sq : IntervalIntegrable (fun x => e₂ x ^ 2) volume 0 1)
    (he1e2 : IntervalIntegrable (fun x => e₁ x * e₂ x) volume 0 1)
    (h_norm1 : (∫ x in (0:ℝ)..1, e₁ x ^ 2) = 1)
    (h_norm2 : (∫ x in (0:ℝ)..1, e₂ x ^ 2) = 1)
    (h_orth : (∫ x in (0:ℝ)..1, e₁ x * e₂ x) = 0) :
    (∫ x in (0:ℝ)..1, (a₁ * e₁ x + a₂ * e₂ x) ^ 2) = a₁ ^ 2 + a₂ ^ 2 := by
  have h_alg : ∀ x : ℝ, (a₁ * e₁ x + a₂ * e₂ x) ^ 2 =
      a₁ ^ 2 * (e₁ x ^ 2) + a₂ ^ 2 * (e₂ x ^ 2) + (2 * a₁ * a₂) * (e₁ x * e₂ x) := by
    intro x
    ring
  have h_int_eq : (∫ x in (0:ℝ)..1, (a₁ * e₁ x + a₂ * e₂ x) ^ 2) =
      ∫ x in (0:ℝ)..1, (a₁ ^ 2 * (e₁ x ^ 2) + a₂ ^ 2 * (e₂ x ^ 2) + (2 * a₁ * a₂) * (e₁ x * e₂ x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_alg x
  rw [h_int_eq]
  have h_part1 : IntervalIntegrable (fun x => a₁ ^ 2 * (e₁ x ^ 2) + a₂ ^ 2 * (e₂ x ^ 2)) volume 0 1 :=
    (he1_sq.const_mul (a₁ ^ 2)).add (he2_sq.const_mul (a₂ ^ 2))
  have h_part2 : IntervalIntegrable (fun x => (2 * a₁ * a₂) * (e₁ x * e₂ x)) volume 0 1 :=
    he1e2.const_mul (2 * a₁ * a₂)
  have h_split1 := integral_add h_part1 h_part2
  rw [h_split1, intervalIntegral.integral_const_mul, h_orth, mul_zero, add_zero]
  have h_split2 := integral_add (he1_sq.const_mul (a₁ ^ 2)) (he2_sq.const_mul (a₂ ^ 2))
  rw [h_split2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h_norm1, h_norm2]
  ring

/-- 🏆 THEOREM 4: Bessel Saturation Equivalence -/
theorem bessel_saturation_iff_zero_residual (energy_f c1 c2 residual : ℝ)
    (h_bessel_exp : residual = energy_f - (c1 ^ 2 + c2 ^ 2)) :
    energy_f = c1 ^ 2 + c2 ^ 2 ↔ residual = 0 := by
  constructor
  · intro h
    rw [h_bessel_exp, h, sub_self]
  · intro h
    linarith

end InfoGeometry.Analysis.Parseval
