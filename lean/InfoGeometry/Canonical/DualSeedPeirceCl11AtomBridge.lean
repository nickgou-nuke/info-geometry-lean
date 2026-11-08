/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Core.DualSeedPeirce

/-!
# Gap 1: Dual Seed Pair → Cl(1,1) Atom Identification

When `Δ = carrierSupport d B = 1`, the dual seed pair induces a `Cl11Atom`:
- `c = Γ = phasePolarization d B` satisfies `c² = Γ² = Δ = 1`
- `d' = J = wheelGenerator d B` satisfies `d'² = J² = -Δ = -1`
- `{c, d'} = {Γ, J} = 0`

Over ℝ with `Δ ≠ 0`, the only dual seed pair is `d = B = 0` (since x² = 0 ⇒ x = 0 in ℝ),
making `carrierSupport d B = 0`. Thus the assumption `carrierSupport d B ≠ 0` is
impossible, and the theorem is vacuously true.

This bridges Stream 9 (Two-Sided Cayley–Dickson Laplace Kernel) with the
Connection Tower base: the Cl(1,1) modular atom is the root upon which the
tensor tower, KMS conditions, and Freudenthal charge space are built.
-/

namespace InfoGeometry.Canonical.DualSeedPeirceCl11AtomBridge

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.DualSeedPeirce.IsDualSeedPair
open InfoGeometry.Core.DiracSuperalgebra

variable {A : Type*} [Ring A]

theorem carrier_support_idem {d B : A} (h : IsDualSeedPair d B) :
    carrierSupport d B * carrierSupport d B = carrierSupport d B := by
  change (polePlus d B + poleMinus d B) * (polePlus d B + poleMinus d B) =
    polePlus d B + poleMinus d B
  rw [add_mul, mul_add, mul_add, pp h, pq h, qp h, qq h]
  abel

theorem phase_wheel_anticommute {d B : A} (h : IsDualSeedPair d B) :
    phasePolarization d B * wheelGenerator d B +
      wheelGenerator d B * phasePolarization d B = 0 := by
  change (polePlus d B - poleMinus d B) * (d - B) + (d - B) * (polePlus d B - poleMinus d B) = 0
  rw [sub_mul, mul_sub, mul_sub, pd h, pb h, qd h, qb h]
  rw [sub_mul, mul_sub, mul_sub, dp h, dq h, bp h, bq h]
  abel

theorem dual_seed_pair_unit_carrier_induces_cl11_atom
    {d B : A} (h : IsDualSeedPair d B) (hΔ : carrierSupport d B = 1) :
    ∃ (c d' : A), c * c = 1 ∧ d' * d' = -1 ∧ c * d' + d' * c = 0 := by
  have hΓ_sq_one : phasePolarization d B * phasePolarization d B = 1 := by
    have h₂ := clifford_squares h
    have h₃ : phasePolarization d B * phasePolarization d B = carrierSupport d B := h₂.2.2
    rw [h₃, hΔ]
  
  have hJ_sq_neg_one : wheelGenerator d B * wheelGenerator d B = -1 := by
    have h₂ := clifford_squares h
    have h₁ : wheelGenerator d B * wheelGenerator d B = -carrierSupport d B := h₂.1
    calc
      wheelGenerator d B * wheelGenerator d B = -carrierSupport d B := by rw [h₁]
      _ = -1 := by
        have h₃ : carrierSupport d B = 1 := hΔ
        calc
          -carrierSupport d B = -(1 : A) := by rw [h₃]
          _ = -1 := by rfl
  
  have h_anticomm : phasePolarization d B * wheelGenerator d B +
      wheelGenerator d B * phasePolarization d B = 0 := by
    exact phase_wheel_anticommute h
  
  refine ⟨phasePolarization d B, wheelGenerator d B, hΓ_sq_one, hJ_sq_neg_one,
    h_anticomm⟩

theorem dual_seed_pair_cl11_over_reals {d B : ℝ} (h : IsDualSeedPair d B) (hΔ_ne_zero : carrierSupport d B ≠ 0) :
    ∃ (c d' : ℝ), c * c = 1 ∧ d' * d' = -1 ∧ c * d' + d' * c = 0 := by
  have h_d_sq_zero : d * d = 0 := h.d_sq
  have h_b_sq_zero : B * B = 0 := h.b_sq
  have h_d_zero : d = 0 := by
    apply mul_self_eq_zero.mp
    exact h_d_sq_zero
  have h_b_zero : B = 0 := by
    have h₁ : B = 0 := by
      apply mul_self_eq_zero.mp
      exact h_b_sq_zero
    exact h₁
  have h_cs_zero : carrierSupport d B = 0 := by
    change d * B + B * d = 0
    subst h_d_zero
    subst h_b_zero
    ring
  exfalso
  exact hΔ_ne_zero h_cs_zero

end InfoGeometry.Canonical.DualSeedPeirceCl11AtomBridge