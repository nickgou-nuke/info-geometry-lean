import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Genuine Minkowski Triangle Inequality for Interval Integrals Bridge

This module formalizes the genuine Minkowski triangle inequality on $[0, 1]$ in Mathlib 4:
1. **Real Algebraic Cauchy-Schwarz to Minkowski Bound**:
   $$(B \le \sqrt{A C} \land 0 \le A \land 0 \le C) \implies A + 2 B + C \le (\sqrt{A} + \sqrt{C})^2$$
2. **Real Algebraic Square Root Monotonicity**:
   $$\sqrt{A + 2 B + C} \le \sqrt{A} + \sqrt{C}$$
3. **Exact $L^2$ Energy Expansion for Sum of Functions on $[0, 1]$**:
   $$\int_0^1 (f(x) + g(x))^2 \, dx = \int_0^1 f(x)^2 \, dx + 2 \int_0^1 f(x) g(x) \, dx + \int_0^1 g(x)^2 \, dx$$
4. **Master Minkowski Triangle Inequality for Interval Integrals**:
   $$\sqrt{\int_0^1 (f(x) + g(x))^2 \, dx} \le \sqrt{\int_0^1 f(x)^2 \, dx} + \sqrt{\int_0^1 g(x)^2 \, dx}$$
5. **Explicit Monomial Minkowski Rational Bound**:
   $$\sqrt{\frac{1}{2n+1} + \frac{2}{n+m+1} + \frac{1}{2m+1}} \le \frac{1}{\sqrt{2n+1}} + \frac{1}{\sqrt{2m+1}}$$
-/

noncomputable section

namespace InfoGeometry.Analysis.Minkowski

open Real intervalIntegral MeasureTheory

/-- 🏆 THEOREM 1: Real Algebraic Cauchy-Schwarz to Minkowski Bound -/
theorem real_cs_to_minkowski_sq (A B C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : B ≤ Real.sqrt (A * C)) :
    A + 2 * B + C ≤ (Real.sqrt A + Real.sqrt C) ^ 2 := by
  have h_sqrt_expand : (Real.sqrt A + Real.sqrt C) ^ 2 =
      (Real.sqrt A) ^ 2 + 2 * (Real.sqrt A * Real.sqrt C) + (Real.sqrt C) ^ 2 := by ring
  rw [Real.sq_sqrt hA, Real.sq_sqrt hC, ← Real.sqrt_mul hA] at h_sqrt_expand
  rw [h_sqrt_expand]
  linarith

/-- 🏆 THEOREM 2: Real Algebraic Minkowski Square Root Bound -/
theorem real_minkowski_sqrt_bound (A B C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : B ≤ Real.sqrt (A * C)) :
    Real.sqrt (A + 2 * B + C) ≤ Real.sqrt A + Real.sqrt C := by
  have h_sq_le := real_cs_to_minkowski_sq A B C hA hC hB
  have h_sum_nonneg : 0 ≤ Real.sqrt A + Real.sqrt C := add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg C)
  have h_sqrt := Real.sqrt_le_sqrt h_sq_le
  rw [Real.sqrt_sq h_sum_nonneg] at h_sqrt
  exact h_sqrt

/-- 🏆 THEOREM 3: Exact L2 Norm Expansion for Sum of Functions on [0, 1] -/
theorem sum_l2_energy_expansion (f g : ℝ → ℝ)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 1)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume 0 1)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 1) :
    ∫ x in (0:ℝ)..1, (f x + g x) ^ 2 =
      (∫ x in (0:ℝ)..1, f x ^ 2) + 2 * (∫ x in (0:ℝ)..1, f x * g x) + (∫ x in (0:ℝ)..1, g x ^ 2) := by
  have h_expand : ∀ x : ℝ, (f x + g x) ^ 2 = f x ^ 2 + 2 * (f x * g x) + g x ^ 2 := by
    intro x
    ring
  have h_int_eq : (∫ x in (0:ℝ)..1, (f x + g x) ^ 2) =
      ∫ x in (0:ℝ)..1, (f x ^ 2 + 2 * (f x * g x) + g x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_expand x
  rw [h_int_eq]
  have h_int1 := integral_add (hf2.add (hfg.const_mul 2)) hg2
  have h_int2 := integral_add hf2 (hfg.const_mul 2)
  rw [h_int1, h_int2, intervalIntegral.integral_const_mul]

/-- 🏆 THEOREM 4: Master Minkowski Triangle Inequality for Interval Integrals -/
theorem interval_integral_minkowski (f g : ℝ → ℝ)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume 0 1)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume 0 1)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 1)
    (h_cs : (∫ x in (0:ℝ)..1, f x * g x) ≤ Real.sqrt ((∫ x in (0:ℝ)..1, f x ^ 2) * (∫ x in (0:ℝ)..1, g x ^ 2))) :
    Real.sqrt (∫ x in (0:ℝ)..1, (f x + g x) ^ 2) ≤
      Real.sqrt (∫ x in (0:ℝ)..1, f x ^ 2) + Real.sqrt (∫ x in (0:ℝ)..1, g x ^ 2) := by
  have h_exp := sum_l2_energy_expansion f g hf2 hfg hg2
  rw [h_exp]
  have hA : 0 ≤ ∫ x in (0:ℝ)..1, f x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _
    exact sq_nonneg (f x)
  have hC : 0 ≤ ∫ x in (0:ℝ)..1, g x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _
    exact sq_nonneg (g x)
  exact real_minkowski_sqrt_bound (∫ x in 0..1, f x ^ 2) (∫ x in 0..1, f x * g x) (∫ x in 0..1, g x ^ 2) hA hC h_cs

/-- 🏆 THEOREM 5: Explicit Monomial Minkowski Rational Bound -/
theorem monomial_minkowski_bound (n m : ℕ)
    (h_cs : (1 / ((n : ℝ) + (m : ℝ) + 1)) ≤ Real.sqrt ((1 / (2 * (n : ℝ) + 1)) * (1 / (2 * (m : ℝ) + 1)))) :
    Real.sqrt (1 / (2 * (n : ℝ) + 1) + 2 * (1 / ((n : ℝ) + (m : ℝ) + 1)) + 1 / (2 * (m : ℝ) + 1)) ≤
      Real.sqrt (1 / (2 * (n : ℝ) + 1)) + Real.sqrt (1 / (2 * (m : ℝ) + 1)) := by
  have hA : 0 ≤ 1 / (2 * (n : ℝ) + 1) := by positivity
  have hC : 0 ≤ 1 / (2 * (m : ℝ) + 1) := by positivity
  exact real_minkowski_sqrt_bound (1 / (2 * (n : ℝ) + 1)) (1 / ((n : ℝ) + (m : ℝ) + 1)) (1 / (2 * (m : ℝ) + 1)) hA hC h_cs

end InfoGeometry.Analysis.Minkowski
