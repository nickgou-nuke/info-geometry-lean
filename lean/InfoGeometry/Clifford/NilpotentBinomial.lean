import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Binomial transport for square-zero operators

This is the algebraic part of the null/horizon calculation. It is stated for
an arbitrary semiring, so no spectral, analytic, or physical interpretation is
being assumed.
-/

namespace InfoGeometry.Clifford.NilpotentBinomial

abbrev SpinorMatrix32 := InfoGeometry.Algebra.FiniteSpin.Mat32R

theorem nsmul_mul_self {R : Type*} [NonUnitalNonAssocSemiring R] (x : R) (hx : x * x = 0) (n : ℕ) :
    (n • x) * x = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [succ_nsmul, add_mul, ih, hx, add_zero]

theorem one_add_pow_of_sq_zero {R : Type*} [Semiring R]
    (x : R) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, nsmul_mul_self x hx n]
      rw [add_zero, add_assoc, succ_nsmul']

theorem one_add_smul_pow_of_sq_zero {R : Type*} [CommSemiring R]
    (x : R) (hx : x * x = 0) (a : R) (n : ℕ) :
    (1 + a • x) ^ n = 1 + n • (a • x) := by
  apply one_add_pow_of_sq_zero
  change (a * x) * (a * x) = 0
  calc
    (a * x) * (a * x) = (a * a) * (x * x) := by ring
    _ = 0 := by rw [hx, mul_zero]

theorem spinorMatrix_one_add_pow_of_sq_zero
    (x : SpinorMatrix32) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  exact one_add_pow_of_sq_zero x hx n

theorem one_add_mul_one_sub_of_sq_zero {R : Type*} [Ring R]
    (x : R) (hx : x * x = 0) :
    (1 + x) * (1 - x) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, hx, add_zero, add_sub_cancel_right]

theorem one_sub_mul_one_add_of_sq_zero {R : Type*} [Ring R]
    (x : R) (hx : x * x = 0) :
    (1 - x) * (1 + x) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, hx, add_zero, add_sub_cancel_right]

theorem isUnit_one_add_of_sq_zero {R : Type*} [Ring R]
    (x : R) (hx : x * x = 0) :
    IsUnit (1 + x) :=
  ⟨⟨1 + x, 1 - x, one_add_mul_one_sub_of_sq_zero x hx, one_sub_mul_one_add_of_sq_zero x hx⟩, rfl⟩

end InfoGeometry.Clifford.NilpotentBinomial
