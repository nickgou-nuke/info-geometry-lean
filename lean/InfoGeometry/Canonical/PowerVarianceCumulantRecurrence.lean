import InfoGeometry.Canonical.PowerVarianceCumulants
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace InfoGeometry.Canonical

/-!
# Power Variance Cumulant Recurrence

This module establishes the differential recurrence relations for the
canonical specializations of the power variance family.

The fundamental recursion is:
  κ_{n+1} = V_ν(μ) * (d/dμ) κ_n

Instead of an abstract differential operator, we provide explicit
`HasDerivAt` lemmas for the cumulant functions, and then show that
the recursive step holds exactly.
-/

/-- Gaussian (ν = 2): V_2(μ) = 1.
For n ≥ 2, κ_n is constant (1 or 0), so its derivative is 0,
which matches κ_{n+1} = 0. -/
theorem hasDerivAt_gaussianCumulant_two (μ : ℝ) :
    HasDerivAt (fun x => gaussianCumulant x 2) 0 μ := by
  have h : (fun x => gaussianCumulant x 2) = fun _ => 1 := by
    ext x
    rw [gaussianCumulant_two]
  rw [h]
  exact hasDerivAt_const _ _

theorem gaussianCumulant_succ_from_variance_deriv_two (μ : ℝ) :
    gaussianCumulant μ 3 = (1 : ℝ) * 0 := by
  rw [gaussianCumulant_eq_zero_of_three_le μ (by omega)]
  ring

/-- Poisson (ν = 1): V_1(μ) = μ.
κ_n = μ, derivative is 1. -/
theorem hasDerivAt_poissonCumulant (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    HasDerivAt (fun x => poissonCumulant x n) 1 μ := by
  have h_eq : (fun x => poissonCumulant x n) = fun x => x := by
    ext x
    rw [poissonCumulant_eq x h]
  rw [h_eq]
  exact hasDerivAt_id μ

theorem poissonCumulant_succ_from_variance_deriv (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    poissonCumulant μ (n + 1) = μ * 1 := by
  rw [poissonCumulant_eq μ (by omega)]
  ring

/-- Gamma (ν = 0): V_0(μ) = μ^2.
κ_n = (n-1)! μ^n, derivative is n! μ^{n-1}. -/
theorem hasDerivAt_gammaCumulant (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    HasDerivAt (fun x => gammaCumulant x n) ((Nat.factorial n : ℝ) * μ ^ (n - 1)) μ := by
  have h_eq : (fun x => gammaCumulant x n) = fun x => (Nat.factorial (n - 1) : ℝ) * x ^ n := by
    ext x
    rw [gammaCumulant_eq_factorial_mul_pow x h]
  rw [h_eq]
  have h_deriv := HasDerivAt.const_mul (Nat.factorial (n - 1) : ℝ) (hasDerivAt_pow n μ)
  -- The derivative of x^n is n * x^{n-1}
  -- So const * n * x^{n-1}
  -- We need to show this equals n! * μ^{n-1}
  have h_fac : (Nat.factorial (n - 1) : ℝ) * ((n : ℝ) * μ ^ (n - 1)) = (Nat.factorial n : ℝ) * μ ^ (n - 1) := by
    have h_fac_nat : (n : ℝ) * (Nat.factorial (n - 1) : ℝ) = (Nat.factorial n : ℝ) := by
      have h_nat : n * Nat.factorial (n - 1) = Nat.factorial n := by
        match n with
        | 0 => contradiction
        | k + 1 => rfl
      exact_mod_cast h_nat
    calc
      (Nat.factorial (n - 1) : ℝ) * ((n : ℝ) * μ ^ (n - 1))
        = ((n : ℝ) * (Nat.factorial (n - 1) : ℝ)) * μ ^ (n - 1) := by ring
      _ = (Nat.factorial n : ℝ) * μ ^ (n - 1) := by rw [h_fac_nat]
  rw [h_fac] at h_deriv
  exact h_deriv

theorem gammaCumulant_succ_from_variance_deriv (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    gammaCumulant μ (n + 1) = μ ^ 2 * ((Nat.factorial n : ℝ) * μ ^ (n - 1)) := by
  rw [gammaCumulant_eq_factorial_mul_pow μ (by omega)]
  have h_sub : n + 1 - 1 = n := Nat.add_sub_cancel n 1
  rw [h_sub]
  calc
    (Nat.factorial n : ℝ) * μ ^ (n + 1)
      = (Nat.factorial n : ℝ) * (μ ^ 2 * μ ^ (n - 1)) := by
        have h_pow : n + 1 = 2 + (n - 1) := by omega
        rw [h_pow, pow_add]
    _ = μ ^ 2 * ((Nat.factorial n : ℝ) * μ ^ (n - 1)) := by ring

end InfoGeometry.Canonical
