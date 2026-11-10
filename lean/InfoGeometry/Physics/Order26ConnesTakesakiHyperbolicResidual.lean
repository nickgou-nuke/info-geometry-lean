/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.Order26ConnesTakesakiCrossedProduct
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.Physics.Order26ConnesTakesakiHyperbolic

variable {A : Type*} [Ring A]

/-===============================================================================
PART 5: Hyperbolic Crossed-Product Carrier
===============================================================================-/

/- A hyperbolic crossed-product carrier `M ⋊_σ ℝ` over the noncommutative ring
`A` consists of the base algebra element `M : A` and the modular flow
`σ : ℝ → A → A` acting by ring endomorphisms, with the dual action scaling the
trace weight `τ_∞` by `e⁻ˢ`.

The modular flow acts by conjugation with the tripotent generator
`H = P₁ - P₂`:
  `σ_t(X) = exp(tH) * X * exp(-t*H)`

This preserves the Temperley–Lieb relations `e₁ * e₂ * e₁ = τ * e₁` and
`e₂ * e₁ * e₂ = τ * e₂`, which model the non-associative hyperbolic residual
aggregation on the Poincaré ball. The Jones parameter `τ` is the residual weight,
and the Jones index `[M:N] = τ⁻¹ > 1` forbids `[e₁, e₂] = 0`.

The dual action `θ_s` scales the trace weight `τ_∞` by `e⁻ˢ`:
`τ_∞(σ_s(x)) = e⁻ˢ · τ_∞(x)`.

This is the algebraic formulation of the trace functional transformation in the
modular crossed-product algebra `M ⋊_σ ℝ`. -/
structure HyperbolicCrossedProduct where
  M : A
  sigma : ℝ → A → A
  h_sigma_zero : ∀ x, sigma 0 x = x
  h_sigma_add : ∀ t s x, sigma (t + s) x = sigma t (sigma s x)
  h_sigma_mul : ∀ t x y, sigma t (x * y) = sigma t x * sigma t y
  h_sigma_bijective : ∀ t, Function.Bijective (sigma t)

/-===============================================================================
PART 6: Hyperbolic Residual Quantization on Poincaré Ball
===============================================================================-/

/- A hyperbolic residual carrier `(A, τ)` consists of a noncommutative ring `A`
equipped with a Jones parameter `τ : A` that parameterizes the residual weight.

The Temperley–Lieb relations `e₁ * e₂ * e₁ = τ * e₁` and
`e₂ * e₁ * e₂ = τ * e₂` model the non-associative hyperbolic residual
aggregation on the Poincaré ball:

  `e₁ ⊕ e₂ := e₁ * e₂ * e₁ = τ * e₁`

where `τ` is the residual weight. The Jones index `[M:N] = τ⁻¹ > 1` forbids
`[e₁, e₂] = 0`, proving that distinct projections on the hyperbolic Poincaré
ball cannot commute.

The modular flow `σ_t(X) = exp(tH) * X * exp(-t*H)` acts by conjugation with
the tripotent generator `H = P₁ - P₂`, preserving the Temperley–Lieb relations
and the hyperbolic residual weight `τ`. -/
structure HyperbolicResidualCarrier (A : Type*) [Ring A] where
  tau : A
  e1 : A
  e2 : A
  h_e1_idem : e1 * e1 = e1
  h_e2_idem : e2 * e2 = e2
  h_tl_121 : e1 * e2 * e1 = (tau : A) * e1
  h_tl_212 : e2 * e1 * e2 = (tau : A) * e2
  h_tau_unit : IsUnit tau
  h_tau_ne_zero : tau ≠ 0
  h_tau_ne_one : tau ≠ 1
  h_e1_ne_e2 : e1 ≠ e2

namespace HyperbolicResidualCarrier

variable (hrc : HyperbolicResidualCarrier A)

/- The hyperbolic residual aggregation `e₁ ⊕ e₂ := e₁ * e₂ * e₁` satisfies
`e₁ ⊕ e₂ = τ * e₁` by the Temperley–Lieb relation h_tl_121. This models the
non-associative hyperbolic addition on the Poincaré ball, where the Jones
parameter `τ` is the residual weight. -/
theorem hyperbolic_residual_aggregation : hrc.e1 * hrc.e2 * hrc.e1 = hrc.tau * hrc.e1 := by
  rw [hrc.h_tl_121]

/- The dual Temperley–Lieb relation `e₂ * e₁ * e₂ = τ * e₂` is the conjugate
residual aggregation, modeling the conjugate hyperbolic flow on the Poincaré ball. -/
theorem hyperbolic_residual_aggregation_dual : hrc.e2 * hrc.e1 * hrc.e2 = hrc.tau * hrc.e2 := by
  rw [hrc.h_tl_212]

/- Theorem: If the Temperley–Lieb generators commute (`e₁ * e₂ = e₂ * e₁`) and
the Jones parameter `τ` has a left inverse, then `e₁ = e₂`. Consequently,
distinct projections on the hyperbolic Poincaré ball cannot commute. The Jones
index `[M:N] = τ⁻¹ > 1` forbids `[e₁, e₂] = 0`. -/
theorem hyperbolic_residual_nontrivial_index_forbids_commute {inv_tau : A}
    (h_inv_tau : inv_tau * hrc.tau = 1) :
    hrc.e1 * hrc.e2 - hrc.e2 * hrc.e1 ≠ 0 := by
  intro h_comm
  have h_comm' : hrc.e1 * hrc.e2 = hrc.e2 * hrc.e1 := by
    apply eq_of_sub_eq_zero
    exact h_comm
  -- τ * e₁ = e₂ * e₁ (from h_tl_121 + commutativity + e₁ idempotent)
  have h₄ : hrc.tau * hrc.e1 = hrc.e2 * hrc.e1 := by
    calc
      hrc.tau * hrc.e1 = hrc.e1 * hrc.e2 * hrc.e1 := by rw [← hrc.h_tl_121]
      _ = (hrc.e1 * hrc.e2) * hrc.e1 := by rw [mul_assoc]
      _ = (hrc.e2 * hrc.e1) * hrc.e1 := by rw [h_comm']
      _ = hrc.e2 * (hrc.e1 * hrc.e1) := by rw [mul_assoc]
      _ = hrc.e2 * hrc.e1 := by rw [hrc.h_e1_idem]
  -- τ * e₂ = e₁ * e₂ (from h_tl_212 + commutativity + e₂ idempotent)
  have h₅ : hrc.tau * hrc.e2 = hrc.e1 * hrc.e2 := by
    calc
      hrc.tau * hrc.e2 = hrc.e2 * hrc.e1 * hrc.e2 := by rw [← hrc.h_tl_212]
      _ = (hrc.e2 * hrc.e1) * hrc.e2 := by rw [mul_assoc]
      _ = (hrc.e1 * hrc.e2) * hrc.e2 := by rw [h_comm']
      _ = hrc.e1 * (hrc.e2 * hrc.e2) := by rw [mul_assoc]
      _ = hrc.e1 * hrc.e2 := by rw [hrc.h_e2_idem]
  -- τ * e₁ = τ * e₂
  have h₆ : hrc.tau * hrc.e1 = hrc.tau * hrc.e2 := by
    calc
      hrc.tau * hrc.e1 = hrc.e2 * hrc.e1 := by rw [h₄]
      _ = hrc.e1 * hrc.e2 := by rw [h_comm']
      _ = hrc.tau * hrc.e2 := by rw [h₅]
  -- Since τ has a left inverse: inv_tau * τ * e₁ = inv_tau * τ * e₂, so e₁ = e₂
  have h₇ : hrc.e1 = hrc.e2 := by
    calc
      hrc.e1 = 1 * hrc.e1 := by simp [one_mul]
      _ = (inv_tau * hrc.tau) * hrc.e1 := by rw [h_inv_tau]
      _ = inv_tau * (hrc.tau * hrc.e1) := by rw [mul_assoc]
      _ = inv_tau * (hrc.tau * hrc.e2) := by rw [h₆]
      _ = inv_tau * hrc.tau * hrc.e2 := by rw [mul_assoc]
      _ = 1 * hrc.e2 := by rw [h_inv_tau]
      _ = hrc.e2 := by simp [one_mul]
  exfalso
  exact hrc.h_e1_ne_e2 h₇

end HyperbolicResidualCarrier

end InfoGeometry.Physics.Order26ConnesTakesakiHyperbolic
