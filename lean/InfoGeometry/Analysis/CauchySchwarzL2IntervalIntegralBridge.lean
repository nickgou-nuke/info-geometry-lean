import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Genuine Cauchy-Schwarz Inequality for Interval Integrals Bridge

This module formalizes the genuine Cauchy-Schwarz energy inequality on $[0, 1]$ in Mathlib 4:
1. **Quadratic Energy Non-Negativity**:
   $$\int_0^1 (f(x) - c g(x))^2 \, dx \ge 0 \quad (\forall c \in \mathbb{R})$$
2. **Exact Quadratic Expansion**:
   $$\int_0^1 (f - c g)^2 = \int_0^1 f^2 - 2 c \int_0^1 f g + c^2 \int_0^1 g^2$$
3. **Exact Discriminant Bound**:
   $$(\forall c, A - 2 c B + c^2 C \ge 0 \land C > 0) \implies B^2 \le A C$$
4. **Master Cauchy-Schwarz Inequality for Interval Integrals**:
   $$\left(\int_0^1 f(x) g(x) \, dx\right)^2 \le \left(\int_0^1 f(x)^2 \, dx\right) \left(\int_0^1 g(x)^2 \, dx\right)$$
5. **Explicit Monomial Hilbert Gram Matrix Bound**:
   $$\left(\int_0^1 x^n x^m \, dx\right)^2 = \frac{1}{(n+m+1)^2} \le \frac{1}{(2n+1)(2m+1)}$$
-/

noncomputable section

namespace InfoGeometry.Analysis.CauchySchwarz

open Real intervalIntegral MeasureTheory

/-- 🏆 THEOREM 1: Non-Negativity of the Quadratic Energy Integrand -/
theorem quadratic_energy_nonneg (f g : ℝ → ℝ) (c : ℝ) :
    0 ≤ ∫ x in (0:ℝ)..1, (f x - c * g x) ^ 2 := by
  have h_le : (0:ℝ) ≤ 1 := by norm_num
  apply intervalIntegral.integral_nonneg h_le
  intro x _
  exact sq_nonneg (f x - c * g x)

/-- 🏆 THEOREM 2: Exact Quadratic Expansion of the Parametric Energy -/
theorem quadratic_energy_expansion (f g : ℝ → ℝ) (c : ℝ)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 1)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume 0 1)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 1) :
    ∫ x in (0:ℝ)..1, (f x - c * g x) ^ 2 =
      (∫ x in (0:ℝ)..1, f x ^ 2) - 2 * c * (∫ x in (0:ℝ)..1, f x * g x) +
        c ^ 2 * ∫ x in (0:ℝ)..1, g x ^ 2 := by
  have h_expand : ∀ x : ℝ, (f x - c * g x) ^ 2 =
      f x ^ 2 - 2 * c * (f x * g x) + c ^ 2 * g x ^ 2 := by
    intro x
    ring
  have h_int_eq : (∫ x in (0:ℝ)..1, (f x - c * g x) ^ 2) =
      ∫ x in (0:ℝ)..1, (f x ^ 2 - 2 * c * (f x * g x) + c ^ 2 * g x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_expand x
  rw [h_int_eq]
  have h_int1 := integral_add (hf2.sub (hfg.const_mul (2 * c))) (hg2.const_mul (c ^ 2))
  have h_int2 := integral_sub hf2 (hfg.const_mul (2 * c))
  rw [h_int1, h_int2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- 🏆 THEOREM 3: Exact Discriminant Bound Implies Cauchy-Schwarz Inequality in ℝ -/
theorem quadratic_nonneg_discriminant_le_zero (A B C : ℝ) (hC : 0 < C)
    (h_quad : ∀ c : ℝ, 0 ≤ A - 2 * c * B + c ^ 2 * C) :
    B ^ 2 ≤ A * C := by
  have h_min := h_quad (B / C)
  have h_eval : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
    have hC_ne : C ≠ 0 := ne_of_gt hC
    field_simp
    ring
  rw [h_eval] at h_min
  have h_sub_pos : 0 ≤ A - B ^ 2 / C := h_min
  have h_div_le : B ^ 2 / C ≤ A := by linarith
  have h_mul_le : (B ^ 2 / C) * C ≤ A * C := mul_le_mul_of_nonneg_right h_div_le (le_of_lt hC)
  have h_cancel : (B ^ 2 / C) * C = B ^ 2 := by
    have hC_ne : C ≠ 0 := ne_of_gt hC
    exact div_mul_cancel₀ (B ^ 2) hC_ne
  rw [h_cancel] at h_mul_le
  exact h_mul_le

/-- 🏆 THEOREM 4: Master Cauchy-Schwarz Inequality for Interval Integrals -/
theorem interval_integral_cauchy_schwarz (f g : ℝ → ℝ)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 1)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume 0 1)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 1)
    (hg_pos : 0 < ∫ x in (0:ℝ)..1, g x ^ 2) :
    (∫ x in (0:ℝ)..1, f x * g x) ^ 2 ≤
      (∫ x in (0:ℝ)..1, f x ^ 2) * (∫ x in (0:ℝ)..1, g x ^ 2) := by
  have h_quad : ∀ c : ℝ, 0 ≤ (∫ x in (0:ℝ)..1, f x ^ 2) - 2 * c * (∫ x in (0:ℝ)..1, f x * g x) + c ^ 2 * (∫ x in (0:ℝ)..1, g x ^ 2) := by
    intro c
    have h_exp := quadratic_energy_expansion f g c hf2 hfg hg2
    rw [← h_exp]
    exact quadratic_energy_nonneg f g c
  exact quadratic_nonneg_discriminant_le_zero (∫ x in 0..1, f x ^ 2) (∫ x in 0..1, f x * g x) (∫ x in 0..1, g x ^ 2) hg_pos h_quad

/-- 🏆 THEOREM 5: Explicit Monomial Cauchy-Schwarz Rational Inequality in ℝ -/
theorem monomial_cauchy_schwarz_rational (n m : ℕ) :
    (1 / ((n : ℝ) + (m : ℝ) + 1)) ^ 2 ≤
      (1 / (2 * (n : ℝ) + 1)) * (1 / (2 * (m : ℝ) + 1)) := by
  have hn : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hm : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hnm : 0 < (n : ℝ) + (m : ℝ) + 1 := by positivity
  have h_diff : (2 * (n : ℝ) + 1) * (2 * (m : ℝ) + 1) ≤ ((n : ℝ) + (m : ℝ) + 1) ^ 2 := by
    have : ((n : ℝ) + (m : ℝ) + 1) ^ 2 - (2 * (n : ℝ) + 1) * (2 * (m : ℝ) + 1) = ((n : ℝ) - (m : ℝ)) ^ 2 := by ring
    linarith [sq_nonneg ((n : ℝ) - (m : ℝ))]
  have h_inv : 1 / (((n : ℝ) + (m : ℝ) + 1) ^ 2) ≤ 1 / ((2 * (n : ℝ) + 1) * (2 * (m : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h_diff
  have h_lhs : (1 / ((n : ℝ) + (m : ℝ) + 1)) ^ 2 = 1 / (((n : ℝ) + (m : ℝ) + 1) ^ 2) := by
    rw [div_pow, one_pow]
  have h_rhs : (1 / (2 * (n : ℝ) + 1)) * (1 / (2 * (m : ℝ) + 1)) = 1 / ((2 * (n : ℝ) + 1) * (2 * (m : ℝ) + 1)) := by
    rw [one_div_mul_one_div]
  rw [h_lhs, h_rhs]
  exact h_inv

end InfoGeometry.Analysis.CauchySchwarz
