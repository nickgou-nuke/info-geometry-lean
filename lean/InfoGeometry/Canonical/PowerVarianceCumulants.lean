import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfoGeometry.Canonical

/-!
# Power Variance Cumulants

This module formalizes the closed-form cumulants for the three canonical
specializations of the Tweedie/Bregman power variance family:
- Gaussian (ν = 2)
- Poisson (ν = 1)
- Gamma (ν = 0)

These are defined algebraically using only natural powers and factorials,
avoiding the need for real exponentiation or differentiation at this layer.
-/

/-- The cumulants of the Gaussian family (ν = 2).
Only the mean (n = 1) and variance (n = 2) are non-zero. -/
def gaussianCumulant (μ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => μ
  | 2 => 1
  | _ => 0

theorem gaussianCumulant_one (μ : ℝ) : gaussianCumulant μ 1 = μ := rfl

theorem gaussianCumulant_two (μ : ℝ) : gaussianCumulant μ 2 = 1 := rfl

theorem gaussianCumulant_eq_zero_of_three_le (μ : ℝ) {n : ℕ} (h : 3 ≤ n) :
    gaussianCumulant μ n = 0 := by
  match n with
  | 0 => contradiction
  | 1 => contradiction
  | 2 => contradiction
  | n + 3 => rfl

theorem gaussianCumulant_succ_eq_zero (μ : ℝ) {n : ℕ} (h : 2 ≤ n) :
    gaussianCumulant μ (n + 1) = 0 := by
  apply gaussianCumulant_eq_zero_of_three_le
  omega

/-- The cumulants of the Poisson family (ν = 1).
All cumulants (for n ≥ 1) are equal to the mean μ. -/
def poissonCumulant (μ : ℝ) : ℕ → ℝ
  | 0 => 0
  | _ => μ

theorem poissonCumulant_eq (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    poissonCumulant μ n = μ := by
  match n with
  | 0 => contradiction
  | n + 1 => rfl

theorem poissonCumulant_succ (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    poissonCumulant μ (n + 1) = poissonCumulant μ n := by
  rw [poissonCumulant_eq μ (by omega), poissonCumulant_eq μ h]

/-- The cumulants of the Gamma family (ν = 0).
κ_n = (n - 1)! * μ^n for n ≥ 1. -/
def gammaCumulant (μ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (Nat.factorial (n - 1) : ℝ) * μ ^ n

theorem gammaCumulant_eq_factorial_mul_pow (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    gammaCumulant μ n = (Nat.factorial (n - 1) : ℝ) * μ ^ n := by
  have : n ≠ 0 := by omega
  simp [gammaCumulant, this]

theorem gammaCumulant_succ (μ : ℝ) {n : ℕ} (h : 1 ≤ n) :
    gammaCumulant μ (n + 1) = (n : ℝ) * μ * gammaCumulant μ n := by
  rw [gammaCumulant_eq_factorial_mul_pow μ (by omega), gammaCumulant_eq_factorial_mul_pow μ h]
  have h_sub : (n + 1 - 1) = n := Nat.add_sub_cancel n 1
  rw [h_sub]
  have h_fac : (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    have h_fac_nat : Nat.factorial n = n * Nat.factorial (n - 1) := by
      calc Nat.factorial n
        _ = n * Nat.factorial (n - 1) := by
          match n with
          | 0 => contradiction
          | k + 1 => rfl
    exact_mod_cast h_fac_nat
  rw [h_fac]
  calc
    (n : ℝ) * (Nat.factorial (n - 1) : ℝ) * μ ^ (n + 1)
      = (n : ℝ) * (Nat.factorial (n - 1) : ℝ) * (μ ^ n * μ) := by rw [pow_succ]
    _ = (n : ℝ) * μ * ((Nat.factorial (n - 1) : ℝ) * μ ^ n) := by ring

end InfoGeometry.Canonical
