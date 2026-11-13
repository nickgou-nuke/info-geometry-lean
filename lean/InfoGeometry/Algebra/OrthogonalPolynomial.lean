/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentDefectIteration
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial evaluation on mutually annihilating operators

Two-sided annihilation removes every mixed positive-degree monomial. The
constant coefficient must be subtracted once: polynomial evaluation is not
additive on orthogonal inputs unless that coefficient vanishes.

The target ring is arbitrary and need not be commutative. The coefficient map
need not have central image, because only additive evaluation is used.
-/

namespace InfoGeometry.Algebra.OrthogonalPolynomial

variable {R B : Type*} [Semiring R] [Ring B]

/-- Positive powers of a sum split over mutually annihilating operators. -/
theorem add_pow_succ_of_orthogonal {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) (n : ℕ) :
    (x + y) ^ (n + 1) = x ^ (n + 1) + y ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : x ^ (n + 1) * y = 0 := by
        rw [pow_succ, mul_assoc, hxy, mul_zero]
      have hy : y ^ (n + 1) * x = 0 := by
        rw [pow_succ, mul_assoc, hyx, mul_zero]
      rw [pow_succ, ih, add_mul, mul_add, mul_add, hx, hy]
      simp only [add_zero, zero_add, ← pow_succ]

/-- The exact polynomial splitting law includes one constant-term correction. -/
theorem eval₂_add_of_orthogonal (f : R →+* B) (p : Polynomial R) {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) :
    p.eval₂ f (x + y) = p.eval₂ f x + p.eval₂ f y - f (p.coeff 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval₂_add, Polynomial.coeff_add, map_add, hp, hq]
      abel
  | monomial n a =>
      cases n with
      | zero => simp
      | succ n =>
          simp [Polynomial.eval₂_monomial, Polynomial.coeff_monomial,
            add_pow_succ_of_orthogonal hxy hyx, mul_add]

/-- Polynomials with zero constant coefficient split additively. -/
theorem eval₂_add_of_orthogonal_of_coeff_zero (f : R →+* B)
    (p : Polynomial R) (hp : p.coeff 0 = 0) {x y : B}
    (hxy : x * y = 0) (hyx : y * x = 0) :
    p.eval₂ f (x + y) = p.eval₂ f x + p.eval₂ f y := by
  rw [eval₂_add_of_orthogonal f p hxy hyx, hp, map_zero, sub_zero]

end InfoGeometry.Algebra.OrthogonalPolynomial

namespace InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- Once an idempotency defect vanishes, every later positive iterate vanishes. -/
theorem idempotencyDefect_iterates_succ_eq_zero {x : B}
    (hx : idempotencyDefect x = 0) (n : ℕ) :
    idempotencyDefect^[n + 1] x = 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [idempotencyDefect]

end InfoGeometry.Core.IdempotentGraphGrassmannian
