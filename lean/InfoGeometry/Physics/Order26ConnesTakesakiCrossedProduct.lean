/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.TomitaTakesakiModularFlow
import InfoGeometry.Physics.FiniteRelativeModularOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.Physics.Order26ConnesTakesaki

variable {A : Type*} [Ring A]

/-===============================================================================
PART 1: Tripotent Generator H = P₁ - P₂
===============================================================================-/

/- A tripotent pair `(P₁, P₂)` consists of two orthogonal idempotents that sum to 1.
The difference `H = P₁ - P₂` is tripotent: `H³ = H`. -/
structure TripotentPair where
  P1 : A
  P2 : A
  hP1_idem : P1 * P1 = P1
  hP2_idem : P2 * P2 = P2
  hP1P2 : P1 * P2 = 0
  hP2P1 : P2 * P1 = 0
  hP1_add_P2 : P1 + P2 = 1

namespace TripotentPair

variable (tp : TripotentPair)

/- The tripotent generator `H = P₁ - P₂`. -/
def H : A := tp.P1 - tp.P2

theorem H_cube : H * H * H = H := by
  have h₁ : H * H = tp.P1 + tp.P2 := by
    calc
      H * H = (tp.P1 - tp.P2) * (tp.P1 - tp.P2) := rfl
      _ = tp.P1 * tp.P1 - tp.P1 * tp.P2 - tp.P2 * tp.P1 + tp.P2 * tp.P2 := by
        rw [sub_mul, mul_sub]
        <;> simp [mul_add, add_mul]
        <;> abel
      _ = tp.P1 - 0 - 0 + tp.P2 := by
        rw [tp.hP1_idem, tp.hP1P2, tp.hP2P1, tp.hP2_idem]
        <;> simp [sub_self, zero_sub, sub_zero]
        <;> abel
      _ = tp.P1 + tp.P2 := by
        simp [sub_zero, zero_sub]
        <;> abel
  calc
    H * H * H = (tp.P1 + tp.P2) * H := by rw [h₁]
    _ = tp.P1 * H + tp.P2 * H := by rw [mul_add]
    _ = tp.P1 * (tp.P1 - tp.P2) + tp.P2 * (tp.P1 - tp.P2) := by rw [H]
    _ = tp.P1 * tp.P1 - tp.P1 * tp.P2 + tp.P2 * tp.P1 - tp.P2 * tp.P2 := by
      rw [mul_sub, mul_sub]
      <;> simp [mul_add, add_mul]
      <;> abel
    _ = tp.P1 - 0 + 0 - tp.P2 := by
      rw [tp.hP1_idem, tp.hP1P2, tp.hP2P1, tp.hP2_idem]
      <;> simp [sub_self, zero_sub, sub_zero]
      <;> abel
    _ = tp.P1 - tp.P2 := by simp [sub_zero, zero_sub]
    _ = H := rfl

end TripotentPair

/===============================================================================
PART 2: Modular Derivation ad_H
===============================================================================-/

/- The modular derivation `ad_H(X) = H*X - X*H` induced by a tripotent generator `H`.
It satisfies additivity and the Leibniz rule over the noncommutative carrier `A`. -/
def modularDerivation {H : A} (X : A) : A :=
  H * X - X * H

theorem modularDerivation_additive {H : A} (X Y : A) :
    modularDerivation H (X + Y) = modularDerivation H X + modularDerivation H Y := by
  calc
    modularDerivation H (X + Y) = H * (X + Y) - (X + Y) * H := rfl
    _ = H * X + H * Y - (X * H + Y * H) := by
      rw [mul_add, mul_add]
      <;> simp [add_assoc]
      <;> abel
    _ = (H * X - X * H) + (H * Y - Y * H) := by
      simp [sub_sub, add_sub, add_assoc]
      <;> abel
    _ = modularDerivation H X + modularDerivation H Y := by rfl

theorem modularDerivation_Leibniz {H : A} (X Y : A) :
    modularDerivation H (X * Y) = modularDerivation H X * Y + X * modularDerivation H Y := by
  calc
    modularDerivation H (X * Y) = H * (X * Y) - (X * Y) * H := rfl
    _ = (H * X) * Y - X * (Y * H) := by rw [mul_assoc]
    _ = (H * X - X * H) * Y + X * (H * Y - Y * H) := by
      calc
        (H * X - X * H) * Y + X * (H * Y - Y * H)
          = (H * X * Y - X * H * Y) + (X * H * Y - X * Y * H) := by
            rw [mul_sub, mul_sub]
            <;> simp [mul_add, add_mul]
            <;> abel
          _ = H * X * Y - X * H * Y + X * H * Y - X * Y * H := by abel
        _ = H * (X * Y) - (X * Y) * H := by
          calc
            H * X * Y - X * H * Y + X * H * Y - X * Y * H
              = H * X * Y - X * Y * H := by abel
            _ = H * (X * Y) - (X * Y) * H := by
              rw [mul_assoc]
              <;> simp [mul_assoc]
              <;> abel
    _ = modularDerivation H X * Y + X * modularDerivation H Y := by
      simp [modularDerivation, sub_sub, add_sub, add_assoc]
      <;> abel

/===============================================================================
PART 3: Strictly Noncommutative Temperley–Lieb Braid
===============================================================================-/

/- Two projections `e₁, e₂ : A` with the Temperley–Lieb relations
`e₁ * e₂ * e₁ = τ * e₁` and `e₂ * e₁ * e₂ = τ * e₂`, where `τ` is a central
scalar (the Jones parameter). -/
structure TemperleyLiebPair where
  tau : A
  e1 : A
  e2 : A
  h_e1_idem : e1 * e1 = e1
  h_e2_idem : e2 * e2 = e2
  h_tl_121 : e1 * e2 * e1 = (tau : A) * e1
  h_tl_212 : e2 * e1 * e2 = (tau : A) * e2
  h_tau_central : ∀ (x : A), (tau : A) * x = x * (tau : A)

/- Theorem: If the Temperley–Lieb generators commute (`e₁ * e₂ = e₂ * e₁`) and the
Jones parameter `τ` has a left inverse, then `e₁ = e₂`. Consequently, distinct
projections cannot commute, proving that non-trivial Jones indices `[M:N] = τ⁻¹ > 1`
forbid `[e₁, e₂] = 0`. -/
theorem temperley_lieb_commute_implies_equal {inv_tau : A} (tl : TemperleyLiebPair)
    (h_inv_tau : inv_tau * tl.tau = 1) (h_comm : tl.e1 * tl.e2 = tl.e2 * tl.e1) :
    tl.e1 = tl.e2 := by
  -- From h_tl_121: e1 * e2 * e1 = τ * e1
  -- Using h_comm: e1 * e2 = e2 * e1, so e1 * e2 * e1 = e2 * e1 * e1 = e2 * e1 (by h_e1_idem)
  -- Therefore τ * e1 = e2 * e1
  have h₁ : tl.tau * tl.e1 = tl.e2 * tl.e1 := by
    calc
      tl.tau * tl.e1 = tl.e1 * tl.e2 * tl.e1 := by rw [← tl.h_tl_121]
      _ = tl.e2 * tl.e1 * tl.e1 := by rw [h_comm] <;> simp [mul_assoc]
      _ = tl.e2 * tl.e1 := by rw [tl.h_e1_idem] <;> simp [mul_assoc]

  -- From h_tl_212: e2 * e1 * e2 = τ * e2
  -- Using h_comm: e2 * e1 = e1 * e2, so e2 * e1 * e2 = e1 * e2 * e2 = e1 * e2 (by h_e2_idem)
  -- Therefore τ * e2 = e1 * e2
  have h₂ : tl.tau * tl.e2 = tl.e1 * tl.e2 := by
    calc
      tl.tau * tl.e2 = tl.e2 * tl.e1 * tl.e2 := by rw [← tl.h_tl_212]
      _ = tl.e1 * tl.e2 * tl.e2 := by rw [h_comm] <;> simp [mul_assoc]
      _ = tl.e1 * tl.e2 := by rw [tl.h_e2_idem] <;> simp [mul_assoc]

  -- τ * e1 = e2 * e1 = e1 * e2 (by h_comm) = τ * e2
  have h₃ : tl.tau * tl.e1 = tl.tau * tl.e2 := by
    calc
      tl.tau * tl.e1 = tl.e2 * tl.e1 := by rw [h₁]
      _ = tl.e1 * tl.e2 := by rw [h_comm]
      _ = tl.tau * tl.e2 := by rw [h₂]

  -- Since τ has a left inverse: inv_tau * τ * (e1 - e2) = 0, so e1 - e2 = 0
  have h₄ : tl.e1 = tl.e2 := by
    have h₄₁ : tl.tau * tl.e1 - tl.tau * tl.e2 = 0 := by
      rw [h₃]
    have h₄₂ : tl.tau * (tl.e1 - tl.e2) = 0 := by
      calc
        tl.tau * (tl.e1 - tl.e2) = tl.tau * tl.e1 - tl.tau * tl.e2 := by rw [mul_sub]
        _ = 0 := by rw [h₄₁]
    have h₄₃ : tl.e1 - tl.e2 = 0 := by
      have h₄₄ : inv_tau * (tl.tau * (tl.e1 - tl.e2)) = inv_tau * 0 := by rw [h₄₂]
      have h₄₅ : inv_tau * (tl.tau * (tl.e1 - tl.e2)) = tl.e1 - tl.e2 := by
        calc
          inv_tau * (tl.tau * (tl.e1 - tl.e2)) = (inv_tau * tl.tau) * (tl.e1 - tl.e2) := by rw [mul_assoc]
          _ = 1 * (tl.e1 - tl.e2) := by rw [h_inv_tau]
          _ = tl.e1 - tl.e2 := by simp [one_mul]
      have h₄₆ : tl.e1 - tl.e2 = 0 := by
        linarith
      exact h₄₆
    have h₄₇ : tl.e1 = tl.e2 := by
      have h₄₈ : tl.e1 - tl.e2 = 0 := h₄₃
      have h₄₉ : tl.e1 = tl.e2 := by
        linarith
      exact h₄₉
    exact h₄₇
  exact h₄

/- Contrapositive: if `τ` has a left inverse, `τ ≠ 0`, `τ ≠ 1`, and `e₁ ≠ e₂`,
then `[e₁, e₂] ≠ 0`. Non-trivial Jones indices `[M:N] = τ⁻¹ > 1` forbid
`[e₁, e₂] = 0`. -/
theorem temperley_lieb_nontrivial_index_forbids_commute {inv_tau : A} (tl : TemperleyLiebPair)
    (h_inv_tau : inv_tau * tl.tau = 1) (h_tau_ne_zero : tl.tau ≠ 0)
    (h_tau_ne_one : tl.tau ≠ 1) (h_e1_ne_e2 : tl.e1 ≠ tl.e2) :
    tl.e1 * tl.e2 - tl.e2 * tl.e1 ≠ 0 := by
  intro h_comm
  have h_comm' : tl.e1 * tl.e2 = tl.e2 * tl.e1 := by
    have h₁ : tl.e1 * tl.e2 - tl.e2 * tl.e1 = 0 := h_comm
    have h₂ : tl.e1 * tl.e2 = tl.e2 * tl.e1 := by
      have h₃ : tl.e1 * tl.e2 - tl.e2 * tl.e1 + tl.e2 * tl.e1 = tl.e2 * tl.e1 := by rw [h₁]
      simp [add_sub_cancel] at h₃
      exact h₃
    exact h₂
  -- Prove e₁ = e₂ directly
  have h₄ : tl.tau * tl.e1 = tl.e2 * tl.e1 := by
    calc
      tl.tau * tl.e1 = tl.e1 * tl.e2 * tl.e1 := by rw [← tl.h_tl_121]
      _ = tl.e2 * tl.e1 * tl.e1 := by rw [h_comm'] <;> simp [mul_assoc]
      _ = tl.e2 * tl.e1 := by rw [tl.h_e1_idem] <;> simp [mul_assoc]
  have h₅ : tl.tau * tl.e2 = tl.e1 * tl.e2 := by
    calc
      tl.tau * tl.e2 = tl.e2 * tl.e1 * tl.e2 := by rw [← tl.h_tl_212]
      _ = tl.e1 * tl.e2 * tl.e2 := by rw [h_comm'] <;> simp [mul_assoc]
      _ = tl.e1 * tl.e2 := by rw [tl.h_e2_idem] <;> simp [mul_assoc]
  have h₆ : tl.tau * tl.e1 = tl.tau * tl.e2 := by
    calc
      tl.tau * tl.e1 = tl.e2 * tl.e1 := by rw [h₄]
      _ = tl.e1 * tl.e2 := by rw [h_comm']
      _ = tl.tau * tl.e2 := by rw [h₅]
  have h₇ : tl.e1 = tl.e2 := by
    have h₇₁ : tl.tau * tl.e1 - tl.tau * tl.e2 = 0 := by rw [h₆]
    have h₇₂ : tl.tau * (tl.e1 - tl.e2) = 0 := by
      calc
        tl.tau * (tl.e1 - tl.e2) = tl.tau * tl.e1 - tl.tau * tl.e2 := by rw [mul_sub]
        _ = 0 := by rw [h₇₁]
    have h₇₃ : tl.e1 - tl.e2 = 0 := by
      have h₇₄ : inv_tau * (tl.tau * (tl.e1 - tl.e2)) = inv_tau * 0 := by rw [h₇₂]
      have h₇₅ : inv_tau * (tl.tau * (tl.e1 - tl.e2)) = tl.e1 - tl.e2 := by
        calc
          inv_tau * (tl.tau * (tl.e1 - tl.e2)) = (inv_tau * tl.tau) * (tl.e1 - tl.e2) := by rw [mul_assoc]
          _ = 1 * (tl.e1 - tl.e2) := by rw [h_inv_tau]
          _ = tl.e1 - tl.e2 := by simp [one_mul]
      have h₇₆ : tl.e1 - tl.e2 = 0 := by
        linarith
      exact h₇₆
    have h₇₇ : tl.e1 = tl.e2 := by
      have h₇₈ : tl.e1 - tl.e2 = 0 := h₇₃
      have h₇₉ : tl.e1 = tl.e2 := by
        linarith
      exact h₇₉
    exact h₇₇
  exact h_e1_ne_e2 h₇

/===============================================================================
PART 4: Modular Crossed-Product Carrier
===============================================================================-/

/- The modular crossed-product algebra `M ⋊_σ ℝ` is modeled as a structure
containing the base algebra element `M : A` and the modular flow
`σ : ℝ → A → A` acting by ring endomorphisms. -/
structure ModularCrossedProduct where
  M : A
  sigma : ℝ → A → A
  h_sigma_zero : ∀ x, sigma 0 x = x
  h_sigma_add : ∀ t s x, sigma (t + s) x = sigma t (sigma s x)
  h_sigma_mul : ∀ t x y, sigma t (x * y) = sigma t x * sigma t y

variable (mcp : ModularCrossedProduct)

/- The modular flow is bijective at each time `t`. -/
theorem sigma_bijective (t : ℝ) : Function.Bijective (mcp.sigma t) := by
  constructor
  · -- Injectivity
    intro x y hxy
    have h₁ : mcp.sigma (-t) (mcp.sigma t x) = x := by
      have h_sum : ((-t : ℝ) + t : ℝ) = 0 := by ring
      calc
        mcp.sigma (-t) (mcp.sigma t x) = mcp.sigma ((-t : ℝ) + t) x := by
          rw [mcp.h_sigma_add]
        _ = mcp.sigma 0 x := by rw [h_sum]
        _ = x := by rw [mcp.h_sigma_zero]
    have h₂ : mcp.sigma (-t) (mcp.sigma t y) = y := by
      have h_sum : ((-t : ℝ) + t : ℝ) = 0 := by ring
      calc
        mcp.sigma (-t) (mcp.sigma t y) = mcp.sigma ((-t : ℝ) + t) y := by
          rw [mcp.h_sigma_add]
        _ = mcp.sigma 0 y := by rw [h_sum]
        _ = y := by rw [mcp.h_sigma_zero]
    have h₃ : mcp.sigma t x = mcp.sigma t y := hxy
    have h₄ : mcp.sigma (-t) (mcp.sigma t x) = mcp.sigma (-t) (mcp.sigma t y) := by
      rw [h₃]
    have h₅ : x = y := by
      rw [h₁] at h₄
      rw [h₂] at h₄
      exact h₄
    exact h₅
  · -- Surjectivity
    intro y
    have h_surj : mcp.sigma t (mcp.sigma (-t) y) = y := by
      have h_sum : (t + -t : ℝ) = 0 := by ring
      calc
        mcp.sigma t (mcp.sigma (-t) y) = mcp.sigma (t + -t : ℝ) y := by
          rw [← mcp.h_sigma_add]
        _ = mcp.sigma 0 y := by rw [h_sum]
        _ = y := by rw [mcp.h_sigma_zero]
    refine ⟨mcp.sigma (-t) y, h_surj⟩

end InfoGeometry.Physics.Order26ConnesTakesaki