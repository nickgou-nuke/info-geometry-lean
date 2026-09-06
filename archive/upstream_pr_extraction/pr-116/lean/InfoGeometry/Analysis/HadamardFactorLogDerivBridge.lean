import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Genuine Hadamard-Weierstrass Factor Logarithmic Derivative Bridge

This module formalizes genuine, non-vacuous complex differentiation identities in Mathlib 4:
1. **Exact Derivative of Single Hadamard Factor $(1 - s / \rho)$ in $\mathbb{C}$**:
   $$\frac{d}{ds} \left(1 - \frac{s}{\rho}\right) = - \frac{1}{\rho} \quad (\forall \rho \neq 0)$$
2. **Exact Logarithmic Derivative Ratio $f'/f = 1 / (s - \rho)$**:
   $$\frac{\frac{d}{ds} (1 - s / \rho)}{1 - s / \rho} = \frac{1}{s - \rho} \quad (\forall \rho \neq 0, s \neq \rho)$$
3. **General Product Rule for Logarithmic Derivatives in $\mathbb{C}$**:
   $$\frac{(f \cdot g)'}{f \cdot g} = \frac{f'}{f} + \frac{g'}{g}$$
4. **Exact Logarithmic Derivative for Two-Root Hadamard Product**:
   $$\frac{P_2'(s)}{P_2(s)} = \frac{1}{s - \rho_1} + \frac{1}{s - \rho_2}$$
-/

namespace InfoGeometry.Analysis.GenuineHadamard

open Complex

/-- 🏆 THEOREM 1: Exact Derivative of Single Hadamard Factor (1 - s / ρ) in ℂ -/
theorem hadamard_factor_deriv (ρ : ℂ) (s : ℂ) :
    deriv (fun z => 1 - z / ρ) s = - (1 / ρ) := by
  have h_sub : (fun z => 1 - z / ρ) = (fun _ => (1 : ℂ)) - (fun z => z / ρ) := rfl
  rw [h_sub]
  have h_const : DifferentiableAt ℂ (fun _ => (1 : ℂ)) s := differentiableAt_const (1 : ℂ)
  have h_linear : DifferentiableAt ℂ (fun z => z / ρ) s := (differentiableAt_id.div_const ρ)
  have h_deriv_sub := deriv_sub h_const h_linear
  have h_deriv_const : deriv (fun _ => (1 : ℂ)) s = 0 := deriv_const s (1 : ℂ)
  have h_deriv_linear : deriv (fun z => z / ρ) s = 1 / ρ := by
    have h : HasDerivAt (fun z => z / ρ) (1 / ρ) s := (hasDerivAt_id s).div_const ρ
    exact h.deriv
  rw [h_deriv_sub, h_deriv_const, h_deriv_linear, zero_sub]

/-- 🏆 THEOREM 2: Exact Logarithmic Derivative Ratio f'/f = 1 / (s - ρ) -/
theorem hadamard_factor_log_deriv (ρ s : ℂ) (hρ : ρ ≠ 0) :
    (deriv (fun z => 1 - z / ρ) s) / (1 - s / ρ) = 1 / (s - ρ) := by
  rw [hadamard_factor_deriv ρ s]
  have h_denom : 1 - s / ρ = (ρ - s) / ρ := by
    have : (1 : ℂ) = ρ / ρ := (div_self hρ).symm
    rw [this, ← sub_div]
  rw [h_denom]
  have h_cancel : (1 / ρ) / ((ρ - s) / ρ) = 1 / (ρ - s) := div_div_div_cancel_right₀ hρ 1 (ρ - s)
  have h_neg : - (1 / (ρ - s)) = 1 / (s - ρ) := by
    rw [← div_neg, neg_sub]
  calc - (1 / ρ) / ((ρ - s) / ρ) = - ((1 / ρ) / ((ρ - s) / ρ)) := by ring
  _ = - (1 / (ρ - s)) := by rw [h_cancel]
  _ = 1 / (s - ρ) := h_neg

/-- 🏆 THEOREM 3: General Product Rule for Logarithmic Derivatives in ℂ -/
theorem log_deriv_mul (f g : ℂ → ℂ) (s : ℂ)
    (hf : DifferentiableAt ℂ f s) (hg : DifferentiableAt ℂ g s)
    (hf0 : f s ≠ 0) (hg0 : g s ≠ 0) :
    deriv (f * g) s / (f s * g s) = deriv f s / f s + deriv g s / g s := by
  have h_prod := deriv_mul hf hg
  rw [h_prod]
  field_simp

/-- 🏆 THEOREM 4: Exact Logarithmic Derivative for Two-Root Hadamard Product -/
theorem two_root_hadamard_log_deriv (ρ₁ ρ₂ s : ℂ)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0)
    (hf₁ : 1 - s / ρ₁ ≠ 0) (hf₂ : 1 - s / ρ₂ ≠ 0) :
    deriv ((fun z => 1 - z / ρ₁) * (fun z => 1 - z / ρ₂)) s /
      ((1 - s / ρ₁) * (1 - s / ρ₂)) =
      1 / (s - ρ₁) + 1 / (s - ρ₂) := by
  have hd₁ : DifferentiableAt ℂ (fun z => 1 - z / ρ₁) s := by
    apply DifferentiableAt.sub
    · exact differentiableAt_const 1
    · exact differentiableAt_id.div_const ρ₁
  have hd₂ : DifferentiableAt ℂ (fun z => 1 - z / ρ₂) s := by
    apply DifferentiableAt.sub
    · exact differentiableAt_const 1
    · exact differentiableAt_id.div_const ρ₂
  have h_log := log_deriv_mul (fun z => 1 - z / ρ₁) (fun z => 1 - z / ρ₂) s hd₁ hd₂ hf₁ hf₂
  rw [h_log]
  have h1 := hadamard_factor_log_deriv ρ₁ s hρ₁
  have h2 := hadamard_factor_log_deriv ρ₂ s hρ₂
  rw [h1, h2]

end InfoGeometry.Analysis.GenuineHadamard
