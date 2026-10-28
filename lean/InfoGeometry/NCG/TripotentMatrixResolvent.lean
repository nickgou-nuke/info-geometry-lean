/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.TripotentMatrixGeometry
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # Polynomial inverse of a shifted tripotent matrix

The spectral parameter is central; the matrix is arbitrary. The excluded
parameter values are sufficient conditions for this formula, not a claim
that every excluded value is a pole for every tripotent.
-/
namespace InfoGeometry.NCG.TripotentMatrixResolvent

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Polynomial
variable {K : Type*} [CommRing K]

/-- This factorization needs no tripotence or spectral assumption. -/
theorem shift_product_split (T : Matrix n n K) (a : K) :
    (a • (1 : Matrix n n K) - T) * (a • (1 : Matrix n n K) + T) =
      a ^ 2 • (1 - T * T) + (a ^ 2 - 1) • (T * T) := by
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, smul_sub, sub_smul, one_smul]
  module

theorem numerator_left {T : Matrix n n K} (hT : T * T * T = T) (a : K) :
    (a • (1 : Matrix n n K) - T) * ((a ^ 2 - 1) • 1 + a • T + T * T) =
      (a * (a ^ 2 - 1)) • (1 : Matrix n n K) := by
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [← mul_assoc T T T, hT]
  module

theorem numerator_right {T : Matrix n n K} (hT : T * T * T = T) (a : K) :
    ((a ^ 2 - 1) • (1 : Matrix n n K) + a • T + T * T) *
      (a • (1 : Matrix n n K) - T) = (a * (a ^ 2 - 1)) • (1 : Matrix n n K) := by
  simp only [mul_sub, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hT]
  module

end Polynomial

section Inverse
variable {K : Type*} [Field K]

/-- Explicit degree-two polynomial candidate; theorems state its domain of validity. -/
def resolventPolynomial (T : Matrix n n K) (a : K) : Matrix n n K :=
  (a * (a ^ 2 - 1))⁻¹ • ((a ^ 2 - 1) • 1 + a • T + T * T)

theorem shift_mul_resolvent {T : Matrix n n K} (hT : T * T * T = T)
    {a : K} (ha : a ≠ 0) (ha2 : a ^ 2 ≠ 1) :
    (a • (1 : Matrix n n K) - T) * resolventPolynomial T a = 1 := by
  rw [resolventPolynomial, mul_smul_comm, numerator_left hT, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero ha (sub_ne_zero.mpr ha2)), one_smul]

theorem resolvent_mul_shift {T : Matrix n n K} (hT : T * T * T = T)
    {a : K} (ha : a ≠ 0) (ha2 : a ^ 2 ≠ 1) :
    resolventPolynomial T a * (a • (1 : Matrix n n K) - T) = 1 := by
  rw [resolventPolynomial, smul_mul_assoc, numerator_right hT, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero ha (sub_ne_zero.mpr ha2)), one_smul]

/-- Identification with mathlib's actual nonsingular matrix inverse. -/
theorem shift_inv {T : Matrix n n K} (hT : T * T * T = T)
    {a : K} (ha : a ≠ 0) (ha2 : a ^ 2 ≠ 1) :
    (a • (1 : Matrix n n K) - T)⁻¹ = resolventPolynomial T a :=
  Matrix.inv_eq_right_inv (shift_mul_resolvent hT ha ha2)

theorem shift_isUnit {T : Matrix n n K} (hT : T * T * T = T)
    {a : K} (ha : a ≠ 0) (ha2 : a ^ 2 ≠ 1) :
    IsUnit (a • (1 : Matrix n n K) - T) :=
  ⟨⟨a • 1 - T, resolventPolynomial T a,
    shift_mul_resolvent hT ha ha2, resolvent_mul_shift hT ha ha2⟩, rfl⟩

end Inverse
end InfoGeometry.NCG.TripotentMatrixResolvent
