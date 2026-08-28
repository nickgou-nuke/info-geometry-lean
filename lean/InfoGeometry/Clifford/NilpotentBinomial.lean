import Mathlib.Algebra.Ring.Basic

/-!
# Binomial transport for square-zero operators

This is the algebraic part of the null/horizon calculation. It is stated for
an arbitrary semiring, so no spectral, analytic, or physical interpretation is
being assumed.
-/

namespace InfoGeometry.Clifford.NilpotentBinomial

abbrev SpinorMatrix32 := Matrix (Fin 32) (Fin 32) ℝ

theorem nsmul_mul_self {R : Type*} [NonUnitalNonAssocSemiring R] (x : R) (hx : x * x = 0) (n : ℕ) :
    (n • x) * x = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [succ_nsmul, add_mul, ih, hx, zero_add, add_zero]

theorem one_add_pow_of_sq_zero {R : Type*} [Semiring R]
    (x : R) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, nsmul_mul_self x hx n]
      rw [add_zero, add_assoc, succ_nsmul']

theorem spinorMatrix_one_add_pow_of_sq_zero
    (x : SpinorMatrix32) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  exact one_add_pow_of_sq_zero x hx n

end InfoGeometry.Clifford.NilpotentBinomial
