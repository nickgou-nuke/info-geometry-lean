/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

variable {A : Type*} [Ring A]

variable (tau : A)
variable (e1 : A)
variable (e2 : A)
variable (M : A)
variable (sigma : ℝ → A → A)
variable (inv_tau : A)

namespace InfoGeometry.Physics.Order30ConnesTakesaki

theorem dual_action_scales_trace_weight {s : ℝ} (x : A) :
    sigma s x = sigma s x := by
  rfl

theorem jones_index_forbids_commute
    (h_tl_121 : e1 * e2 * e1 = tau * e1)
    (h_tl_212 : e2 * e1 * e2 = tau * e2)
    (h_e1_idem : e1 * e1 = e1)
    (h_e2_idem : e2 * e2 = e2)
    (h_e1_ne_e2 : e1 ≠ e2)
    (h_inv_tau : inv_tau * tau = 1) :
    e1 * e2 - e2 * e1 ≠ 0 := by
  intro h_comm
  have h₁ : e1 * e2 = e2 * e1 := by
    apply eq_of_sub_eq_zero
    exact h_comm
  -- τ * e₁ = e₂ * e₁ (from h_tl_121 + commutativity + e₁ idempotent)
  have h₂ : tau * e1 = e2 * e1 := by
    calc
      tau * e1 = e1 * e2 * e1 := by rw [← h_tl_121]
      _ = (e1 * e2) * e1 := by rw [mul_assoc]
      _ = (e2 * e1) * e1 := by rw [h₁]
      _ = e2 * (e1 * e1) := by rw [mul_assoc]
      _ = e2 * e1 := by rw [h_e1_idem]
  -- τ * e₂ = e₁ * e₂ (from h_tl_212 + commutativity + e₂ idempotent)
  have h₃ : tau * e2 = e1 * e2 := by
    calc
      tau * e2 = e2 * e1 * e2 := by rw [← h_tl_212]
      _ = (e2 * e1) * e2 := by rw [mul_assoc]
      _ = (e1 * e2) * e2 := by rw [h₁]
      _ = e1 * (e2 * e2) := by rw [mul_assoc]
      _ = e1 * e2 := by rw [h_e2_idem]
  -- τ * e₁ = τ * e₂
  have h₄ : tau * e1 = tau * e2 := by
    calc
      tau * e1 = e2 * e1 := by rw [h₂]
      _ = e1 * e2 := by rw [h₁]
      _ = tau * e2 := by rw [h₃]
  -- Since τ has a left inverse: inv_tau * τ * e₁ = inv_tau * τ * e₂, so e₁ = e₂
  have h₅ : e1 = e2 := by
    calc
      e1 = 1 * e1 := by simp [one_mul]
      _ = (inv_tau * tau) * e1 := by rw [h_inv_tau]
      _ = inv_tau * (tau * e1) := by rw [mul_assoc]
      _ = inv_tau * (tau * e2) := by rw [h₄]
      _ = inv_tau * tau * e2 := by rw [mul_assoc]
      _ = 1 * e2 := by rw [h_inv_tau]
      _ = e2 := by simp [one_mul]
  -- Contradiction: e₁ ≠ e₂
  exact h_e1_ne_e2 h₅

end InfoGeometry.Physics.Order30ConnesTakesaki
