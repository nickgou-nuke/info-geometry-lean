/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedPeirce
import Mathlib.Algebra.Lie.Sl2

/-!
# Native Cartan triples from the existing reflexive square-zero seeds

No commutativity is assumed. The existing `IsDualSeedPair` supplies exactly
square-zero and reflexivity equations. A nonzero seed is required for the
native `IsSl2Triple`; the zero triple is not accepted as a nontrivial triple.
The support identities below are algebraic, not analytic spectral estimates.
-/

namespace InfoGeometry.Core.DualSeedPeirce.IsDualSeedPair

open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Singular.MoorePenrose

variable {A B : Type*} [Ring A] [Ring B] {d b : A}

theorem phase_mul_seed (h : IsDualSeedPair d b) :
    phasePolarization d b * d = d := by
  change (polePlus d b - poleMinus d b) * d = d
  rw [sub_mul, h.pd, h.qd, sub_zero]

theorem seed_mul_phase (h : IsDualSeedPair d b) :
    d * phasePolarization d b = -d := by
  change d * (polePlus d b - poleMinus d b) = -d
  rw [mul_sub, h.dp, h.dq, zero_sub]

theorem phase_mul_partner (h : IsDualSeedPair d b) :
    phasePolarization d b * b = -b := by
  change (polePlus d b - poleMinus d b) * b = -b
  rw [sub_mul, h.pb, h.qb, zero_sub]

theorem partner_mul_phase (h : IsDualSeedPair d b) :
    b * phasePolarization d b = b := by
  change b * (polePlus d b - poleMinus d b) = b
  rw [mul_sub, h.bp, h.bq, sub_zero]

theorem lie_phase_seed (h : IsDualSeedPair d b) :
    ⁅phasePolarization d b, d⁆ = (2 : ℕ) • d := by
  change phasePolarization d b * d - d * phasePolarization d b = _
  rw [h.phase_mul_seed, h.seed_mul_phase, sub_neg_eq_add, two_nsmul]

theorem lie_phase_partner (h : IsDualSeedPair d b) :
    ⁅phasePolarization d b, b⁆ = -((2 : ℕ) • b) := by
  change phasePolarization d b * b - b * phasePolarization d b = _
  rw [h.phase_mul_partner, h.partner_mul_phase, two_nsmul]
  abel

theorem phase_ne_zero (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    phasePolarization d b ≠ 0 := by
  intro hz
  apply hd
  have he := h.phase_mul_seed
  rw [hz, zero_mul] at he
  exact he.symm

/-- Genuine noncommutativity follows from reflexivity and a nonzero seed. -/
theorem seeds_not_commute (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    ¬ Commute d b := by
  intro hc
  apply h.phase_ne_zero hd
  change d * b - b * d = 0
  exact sub_eq_zero.mpr hc.eq

/-- A native Mathlib `sl₂` triple, including its nondegeneracy field. -/
theorem isSl2Triple (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    IsSl2Triple (phasePolarization d b) d b where
  h_ne_zero := h.phase_ne_zero hd
  lie_e_f := rfl
  lie_h_e_nsmul := h.lie_phase_seed
  lie_h_f_nsmul := h.lie_phase_partner

theorem support_idempotent (h : IsDualSeedPair d b) :
    carrierSupport d b * carrierSupport d b = carrierSupport d b := by
  change (polePlus d b + poleMinus d b) *
    (polePlus d b + poleMinus d b) = polePlus d b + poleMinus d b
  rw [add_mul, mul_add, mul_add, h.pp, h.pq, h.qp, h.qq]
  simp only [add_zero, zero_add]

theorem support_mul_seed (h : IsDualSeedPair d b) :
    carrierSupport d b * d = d := by
  change (polePlus d b + poleMinus d b) * d = d
  rw [add_mul, h.pd, h.qd, add_zero]

theorem support_ne_zero (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    carrierSupport d b ≠ 0 := by
  intro hz
  apply hd
  have he := h.support_mul_seed
  rw [hz, zero_mul] at he
  exact he.symm

/-- The normalization is the usual integral quadratic Casimir expression. -/
theorem quadratic_casimir (h : IsDualSeedPair d b) :
    phasePolarization d b * phasePolarization d b +
      (2 : ℕ) • carrierSupport d b = (3 : ℕ) • carrierSupport d b := by
  rw [h.clifford_squares.2.2]
  abel

theorem support_mul_velocity (h : IsDualSeedPair d b) :
    carrierSupport d b * transitionVelocity d b = transitionVelocity d b := by
  change (polePlus d b + poleMinus d b) * (d + b) = d + b
  rw [add_mul, mul_add, mul_add, h.pd, h.pb, h.qd, h.qb]
  simp only [add_zero, zero_add]

theorem velocity_mul_support (h : IsDualSeedPair d b) :
    transitionVelocity d b * carrierSupport d b = transitionVelocity d b := by
  change (d + b) * (polePlus d b + poleMinus d b) = d + b
  rw [add_mul, mul_add, mul_add, h.dp, h.dq, h.bp, h.bq]
  simp only [add_zero, zero_add]

theorem completed_velocity_involution (h : IsDualSeedPair d b) :
    (1 - carrierSupport d b + transitionVelocity d b) *
      (1 - carrierSupport d b + transitionVelocity d b) = 1 := by
  have hkk := h.support_idempotent
  have hee := h.clifford_squares.2.1
  have hke := h.support_mul_velocity
  have hek := h.velocity_mul_support
  noncomm_ring [hkk, hee, hke, hek]

/-- Preservation under an actual unital ring homomorphism. -/
theorem map (h : IsDualSeedPair d b) (φ : A →+* B) :
    IsDualSeedPair (φ d) (φ b) where
  d_sq := by rw [← map_mul, h.d_sq, map_zero]
  b_sq := by rw [← map_mul, h.b_sq, map_zero]
  inner := by rw [← map_mul, ← map_mul, h.inner]
  outer := by rw [← map_mul, ← map_mul, h.outer]

/-- Injectivity, not polynomial preservation alone, preserves nondegeneracy. -/
theorem isSl2Triple_map (h : IsDualSeedPair d b) (hd : d ≠ 0)
    (φ : A →+* B) (hφ : Function.Injective φ) :
    IsSl2Triple (phasePolarization (φ d) (φ b)) (φ d) (φ b) := by
  apply (h.map φ).isSl2Triple
  intro hz
  apply hd
  apply hφ
  simpa only [map_zero] using hz

end InfoGeometry.Core.DualSeedPeirce.IsDualSeedPair
