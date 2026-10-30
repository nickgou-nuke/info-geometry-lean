/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentGraphGrassmannian
import Mathlib.Logic.Function.Iterate

/-!
# Finite iteration of the idempotency defect

Orthogonality in each multiplication order persists under the defect map.
Consequently every finite iterate splits across mutually orthogonal inputs.
Ring homomorphisms transport the entire finite orbit.
-/

namespace InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B C : Type*} [Ring B] [Ring C]

/-- One-sided annihilation suffices for the ordered product of defects. -/
theorem idempotencyDefect_mul_eq_zero {x y : B} (hxy : x * y = 0) :
    idempotencyDefect x * idempotencyDefect y = 0 := by
  have h : x * (y * y) = 0 := by rw [← mul_assoc, hxy, zero_mul]
  simp only [idempotencyDefect, sub_mul, mul_sub, mul_assoc, h, hxy,
    mul_zero, sub_self]

theorem idempotencyDefect_iterates_mul_eq_zero {x y : B}
    (hxy : x * y = 0) (n : ℕ) :
    idempotencyDefect^[n] x * idempotencyDefect^[n] y = 0 := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact idempotencyDefect_mul_eq_zero ih

/-- The full finite defect orbit splits over orthogonal ring elements. -/
theorem idempotencyDefect_iterates_add_of_orthogonal {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) (n : ℕ) :
    idempotencyDefect^[n] (x + y) =
      idempotencyDefect^[n] x + idempotencyDefect^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact idempotencyDefect_add_of_orthogonal
      (idempotencyDefect_iterates_mul_eq_zero hxy n)
      (idempotencyDefect_iterates_mul_eq_zero hyx n)

theorem map_idempotencyDefect_iterates (f : B →+* C) (x : B) (n : ℕ) :
    f (idempotencyDefect^[n] x) = idempotencyDefect^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', map_idempotencyDefect, ih]

/-- The defect polynomial transports an operator intertwining equation. -/
theorem idempotencyDefect_intertwines {x y z : B} (h : x * y = y * z) :
    idempotencyDefect x * y = y * idempotencyDefect z := by
  unfold idempotencyDefect
  calc
    (x * x - x) * y = x * (x * y) - x * y := by noncomm_ring
    _ = x * (y * z) - y * z := by rw [h]
    _ = (x * y) * z - y * z := by rw [mul_assoc]
    _ = (y * z) * z - y * z := by rw [h]
    _ = y * (z * z - z) := by noncomm_ring

/-- Every finite iterate preserves the same intertwiner, without commutativity. -/
theorem idempotencyDefect_iterates_intertwines {x y z : B}
    (h : x * y = y * z) (n : ℕ) :
    idempotencyDefect^[n] x * y = y * idempotencyDefect^[n] z := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact idempotencyDefect_intertwines ih

/-- Left support survives every finite defect iterate. -/
theorem idempotencyDefect_iterates_left_support {p x : B}
    (h : p * x = x) (n : ℕ) : p * idempotencyDefect^[n] x =
      idempotencyDefect^[n] x := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply', idempotencyDefect, mul_sub,
      ← mul_assoc, ih]

/-- Right support survives every finite defect iterate. -/
theorem idempotencyDefect_iterates_right_support {p x : B}
    (h : x * p = x) (n : ℕ) : idempotencyDefect^[n] x * p =
      idempotencyDefect^[n] x := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply', idempotencyDefect, sub_mul,
      mul_assoc, ih]

end InfoGeometry.Core.IdempotentGraphGrassmannian
