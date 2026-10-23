/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic

/-! Exact vanishing criterion for symmetric overlap in arbitrary rings.
Only the first endpoint is required to be idempotent. -/
namespace InfoGeometry.Core.IdempotentSymmetricOverlap

variable {R : Type*} [Ring R] {p q : R}

/-- Symmetric overlap can vanish through two-torsion, rather than orthogonality. -/
theorem symmetric_overlap_zero_iff (hp : p * p = p) :
    p * q + q * p = 0 ↔ p * q = q * p ∧ p * q + p * q = 0 := by
  constructor
  · intro hz
    have hl : p * q + p * q * p = 0 := by
      have h := congrArg (fun x => p * x) hz
      simpa only [mul_add, ← mul_assoc, hp, mul_zero] using h
    have hr : p * q * p + q * p = 0 := by
      have h := congrArg (fun x => x * p) hz
      simpa only [add_mul, mul_assoc, hp, zero_mul] using h
    have hc : p * q = q * p := by
      calc
        p * q = -(p * q * p) := eq_neg_of_add_eq_zero_left hl
        _ = q * p := (eq_neg_of_add_eq_zero_right hr).symm
    exact ⟨hc, by simpa only [← hc] using hz⟩
  · rintro ⟨hc, hz⟩
    simpa only [← hc] using hz

end InfoGeometry.Core.IdempotentSymmetricOverlap
