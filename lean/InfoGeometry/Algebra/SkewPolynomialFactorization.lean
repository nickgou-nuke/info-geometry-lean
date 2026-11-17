/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Tactic.Abel

/-!
# Ordered factorization in native skew polynomials

The twist is Mathlib's actual `SkewPolynomial.φ`, obtained from the action
defining multiplication on `SkewPolynomial R`. The coefficient ring may be
noncommutative. The factorization and its defect retain the order of every
coefficient product.

These statements concern polynomial multiplication. They do not identify
Ore right roots with ordinary substitution roots or construct a crossed
product, an Azumaya algebra, or a geometric covering space.
-/

namespace InfoGeometry.Algebra.SkewPolynomialFactorization

open SkewPolynomial

variable {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℕ) R]

private theorem X_mul_constant (a : R) :
    (X : SkewPolynomial R) * C a = C (φ a) * X := by
  calc
    (X : SkewPolynomial R) * C a = X * monomial 0 a := by
      rw [monomial_zero_left]
    _ = monomial 1 (φ a) := by
      simpa only [zero_add] using X_mul_monomial 0 a
    _ = C (φ a) * X := (C_mul_X_eq_monomial).symm

/-- The linear coefficient records the actual twist of the right factor. -/
theorem ordered_factor_expansion (u v : R) :
    (X - C u : SkewPolynomial R) * (X + C v) =
      X ^ 2 + C (φ v - u) * X - C (u * v) := by
  calc
    (X - C u : SkewPolynomial R) * (X + C v) =
        X * X + C (φ v) * X - (C u * X + C (u * v)) := by
      rw [sub_mul, mul_add, mul_add, X_mul_constant, ← C_mul]
    _ = X ^ 2 + C (φ v - u) * X - C (u * v) := by
      rw [map_sub, sub_mul, pow_two]
      abel

/-- A right inverse paired with its twist gives an exact factorization. -/
theorem twisted_inverse_factorization (u v : R)
    (htwist : φ v = u) (hinverse : u * v = 1) :
    (X - C u : SkewPolynomial R) * (X + C v) = X ^ 2 - 1 := by
  simpa only [htwist, hinverse, sub_self, map_zero, zero_mul, add_zero, C_1]
    using ordered_factor_expansion u v

/-- Ordinary difference of squares has an explicit ordered linear defect. -/
theorem ordered_difference_of_squares_defect (u : R) :
    (X - C u : SkewPolynomial R) * (X + C u) -
        (X ^ 2 - C (u ^ 2)) = C (φ u - u) * X := by
  rw [ordered_factor_expansion, pow_two u]
  abel

/-- The ordinary formula is valid exactly at fixed points of the twist. -/
theorem ordered_difference_of_squares_iff (u : R) :
    (X - C u : SkewPolynomial R) * (X + C u) =
        X ^ 2 - C (u ^ 2) ↔ φ u = u := by
  rw [← sub_eq_zero, ordered_difference_of_squares_defect]
  constructor
  · intro h
    have hcoeff := congrArg (fun p : SkewPolynomial R => coeff p 1) h
    rw [C_mul_X_eq_monomial] at hcoeff
    have hzero : φ u - u = 0 := by
      simpa [coeff_monomial] using hcoeff
    exact sub_eq_zero.mp hzero
  · intro h
    simp only [h, sub_self, map_zero, zero_mul]

end InfoGeometry.Algebra.SkewPolynomialFactorization
