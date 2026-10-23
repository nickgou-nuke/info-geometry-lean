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

/-- An inner inverse suffices: symmetric overlap vanishes exactly when the
support idempotents commute and the square has additive order dividing two.
Neither an involution nor an outer-inverse axiom is required. -/
theorem inner_inverse_symmetric_overlap_zero_iff {a m : R} (h : a * m * a = a) :
    (a * m) * (m * a) + (m * a) * (a * m) = 0 ↔
      (a * m) * (m * a) = (m * a) * (a * m) ∧
      a * a + a * a = 0 := by
  have hp : (a * m) * (a * m) = a * m := by
    calc
      (a * m) * (a * m) = (a * m * a) * m := by simp only [mul_assoc]
      _ = a * m := by rw [h]
  have recover : a * ((m * a) * (a * m)) * a = a * a := by
    calc
      a * ((m * a) * (a * m)) * a = (a * m * a) * (a * m * a) := by
        simp only [mul_assoc]
      _ = a * a := by rw [h]
  constructor
  · intro hz
    obtain ⟨hc, ht⟩ :=
      (symmetric_overlap_zero_iff hp).mp hz
    refine ⟨hc, ?_⟩
    rw [hc] at ht
    have hs := congrArg (fun x => a * x * a) ht
    simpa only [mul_add, add_mul, recover, mul_zero, zero_mul] using hs
  · rintro ⟨hc, ht⟩
    have hs := congrArg (fun x => m * x * m) ht
    have hz : (m * a) * (a * m) + (m * a) * (a * m) = 0 := by
      simpa only [mul_add, add_mul, mul_assoc, mul_zero, zero_mul] using hs
    simpa only [hc] using hz

end InfoGeometry.Core.IdempotentSymmetricOverlap
