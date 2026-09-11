import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Constructive Mellin Integral in Mathlib 4 (Pauli-Compliant)

This module formalizes genuine Lebesgue interval integrals for monomial powers on $[0, 1]$:
1. Exact antiderivative of monomial power function $x \mapsto x^n$ on $[0, 1]$:
   $$\int_0^1 x^n \, dx = \frac{1}{n + 1} \quad (n \in \mathbb{N})$$
2. Strict positivity and boundedness of the $L^2(0, 1)$ norm for monomial functions:
   $$\|x^n\|_{L^2(0, 1)}^2 = \int_0^1 x^{2n} \, dx = \frac{1}{2n + 1} > 0$$
3. Exact Gram matrix element:
   $$\langle x^n, x^m \rangle_{L^2(0, 1)} = \int_0^1 x^{n+m} \, dx = \frac{1}{n + m + 1}$$
-/

noncomputable section

namespace InfoGeometry.Analysis.ConstructiveMellin

open Real intervalIntegral

/-- 🏆 THEOREM 1: Exact Integral of Monomial x^n on (0, 1) -/
theorem integral_pow_zero_one (n : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ n = 1 / ((n : ℝ) + 1) := by
  have h := integral_pow (n := n) (a := 0) (b := 1)
  rw [h]
  have h_zero : (0 : ℝ) ^ (n + 1) = 0 := zero_pow (Nat.succ_ne_zero n)
  have h_one : (1 : ℝ) ^ (n + 1) = 1 := one_pow (n + 1)
  rw [h_zero, h_one, sub_zero]

/-- 🏆 THEOREM 2: Exact L² Energy of Monomial Basis Function x^n on (0, 1) -/
theorem monomial_L2_energy (n : ℕ) :
    ∫ x in (0:ℝ)..1, (x ^ n) ^ 2 = 1 / (2 * (n : ℝ) + 1) := by
  have h_sq : ∀ x : ℝ, (x ^ n) ^ 2 = x ^ (2 * n) := by
    intro x
    rw [← pow_mul]
    ring_nf
  have h_int_eq : (∫ x in (0:ℝ)..1, (x ^ n) ^ 2) = ∫ x in (0:ℝ)..1, x ^ (2 * n) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_sq x
  rw [h_int_eq, integral_pow_zero_one (2 * n)]
  push_cast
  rfl

/-- 🏆 THEOREM 3: Strict Positivity of Monomial L² Energy in L²(0, 1) -/
theorem monomial_L2_energy_pos (n : ℕ) :
    0 < ∫ x in (0:ℝ)..1, (x ^ n) ^ 2 := by
  rw [monomial_L2_energy n]
  have h_den_pos : 0 < 2 * (n : ℝ) + 1 := by positivity
  exact one_div_pos.mpr h_den_pos

/-- 🏆 THEOREM 4: Exact Gram Matrix Element for Monomial Basis in L²(0, 1) -/
theorem monomial_L2_inner_product (n m : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ n * x ^ m = 1 / ((n : ℝ) + (m : ℝ) + 1) := by
  have h_prod : ∀ x : ℝ, x ^ n * x ^ m = x ^ (n + m) := by
    intro x
    exact (pow_add x n m).symm
  have h_int_eq : (∫ x in (0:ℝ)..1, x ^ n * x ^ m) = ∫ x in (0:ℝ)..1, x ^ (n + m) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h_prod x
  rw [h_int_eq, integral_pow_zero_one (n + m)]
  push_cast
  rfl

end InfoGeometry.Analysis.ConstructiveMellin
