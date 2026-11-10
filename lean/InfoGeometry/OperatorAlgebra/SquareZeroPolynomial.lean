/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.NoncommRing

/-!
# Polynomial evaluation along square-zero operator directions

The ambient algebra is allowed to be noncommutative. Exact first-order
polynomial evaluation at a base `x` uses the explicit hypothesis `Commute x N`.
The scalar-base specialization therefore applies to every square-zero operator.

A Peirce shear is a different exact identity: if `P * N = N` and `N * P = 0`,
then `P + N` is idempotent and its polynomial response is the divided difference
`F.eval 1 - F.eval 0`. No differentiability or convergence assumption is hidden
in either algebraic statement. The exponential below is Mathlib's finite
nilpotent exponential, not a newly defined analytic exponential.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPolynomial

open Polynomial

section PureRingPeirceShear

variable {A : Type*} [Ring A]

/-- The two directional Peirce relations already force square-zero
nilpotency over any ring `[Ring A]`. In particular, nonzero is a separate condition. -/
theorem sq_zero_of_peirce_relations {P N : A}
    (hPN : P * N = N) (hNP : N * P = 0) : N * N = 0 := by
  calc
    N * N = N * (P * N) := by rw [hPN]
    _ = (N * P) * N := (mul_assoc N P N).symm
    _ = 0 := by rw [hNP, zero_mul]

/-- Adding one oriented off-diagonal corner to an idempotent gives an
idempotent over any ring `[Ring A]` even though the two operators need not commute. -/
theorem add_idempotent_of_peirce_relations {P N : A} (hP : P * P = P)
    (hPN : P * N = N) (hNP : N * P = 0) :
    (P + N) * (P + N) = P + N := by
  have hN := sq_zero_of_peirce_relations hPN hNP
  noncomm_ring [hP, hPN, hNP, hN]

end PureRingPeirceShear

section Polynomial

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Exact polynomial Taylor evaluation when the base commutes with the
square-zero direction; the ambient algebra need not be commutative. -/
theorem aeval_add_of_commute_sq_zero (F : R[X]) {x N : A}
    (hxN : Commute x N) (hN : N * N = 0) :
    aeval (x + N) F = aeval x F + aeval x F.derivative * N := by
  have step (q : R[X])
      (hq : aeval (x + N) q = aeval x q + aeval x q.derivative * N) :
      aeval (x + N) (q * X) =
        aeval x (q * X) + aeval x (q * X).derivative * N := by
    simp only [aeval_mul, aeval_X, derivative_mul, derivative_X, mul_one,
      map_add, hq]
    noncomm_ring [hxN.symm.eq, hN]
  refine Polynomial.induction_on F ?_ ?_ ?_
  · intro r
    simp
  · intro p q hp hq
    simp only [aeval_add, derivative_add, hp, hq, add_mul]
    abel
  · intro n r ih
    simpa only [pow_succ, mul_assoc] using step (C r * X ^ n) ih

/-- At a central scalar base, every square-zero direction gives an exact
first-order formula with the native formal polynomial derivative. -/
theorem aeval_scalar_add_sq_zero (F : R[X]) (r : R) {N : A}
    (hN : N * N = 0) :
    aeval (algebraMap R A r + N) F =
      algebraMap R A (F.eval r) + F.derivative.eval r • N := by
  simpa only [aeval_algebraMap_apply_eq_algebraMap_eval, Algebra.smul_def] using
    aeval_add_of_commute_sq_zero F (Algebra.commutes r N) hN

/-- Polynomial evaluation at an idempotent is determined by the values at
zero and one, inside the full ambient algebra. -/
theorem aeval_idempotent (F : R[X]) {P : A} (hP : P * P = P) :
    aeval P F = algebraMap R A (F.eval 0) + (F.eval 1 - F.eval 0) • P := by
  have step (q : R[X])
      (hq : aeval P q =
        algebraMap R A (q.eval 0) + (q.eval 1 - q.eval 0) • P) :
      aeval P (q * X) =
        algebraMap R A ((q * X).eval 0) +
          ((q * X).eval 1 - (q * X).eval 0) • P := by
    simp only [aeval_mul, aeval_X, eval_mul, eval_X, mul_zero, mul_one,
      map_zero, sub_zero, zero_add, hq, Algebra.smul_def, map_sub]
    noncomm_ring [hP]
  refine Polynomial.induction_on F ?_ ?_ ?_
  · intro r
    simp
  · intro p q hp hq
    simp only [eval_add, hp, hq, Algebra.smul_def, map_add, map_sub]
    noncomm_ring
  · intro n r ih
    simpa only [pow_succ, mul_assoc] using step (C r * X ^ n) ih

/-- Exact polynomial response to an oriented Peirce shear. Its coefficient
is the divided difference at zero and one, not `F.derivative.eval 1`. -/
theorem aeval_peirce_shear (F : R[X]) {P N : A} (hP : P * P = P)
    (hPN : P * N = N) (hNP : N * P = 0) :
    aeval (P + N) F = aeval P F + (F.eval 1 - F.eval 0) • N := by
  rw [aeval_idempotent F (add_idempotent_of_peirce_relations hP hPN hNP),
    aeval_idempotent F hP, smul_add]
  abel

/-- The whole scalar-parameter Peirce shear has exact polynomial response,
with no limit or remainder construction. -/
theorem aeval_peirce_smul_shear (F : R[X]) (t : R) {P N : A}
    (hP : P * P = P) (hPN : P * N = N) (hNP : N * P = 0) :
    aeval (P + t • N) F = aeval P F + (F.eval 1 - F.eval 0) • (t • N) := by
  apply aeval_peirce_shear F hP
  · rw [mul_smul_comm, hPN]
  · rw [smul_mul_assoc, hNP, smul_zero]

end Polynomial

section NoncommutativeResidual

variable {A : Type*} [Ring A]

/-- Square-zero alone does not suppress separated occurrences of the
direction: the cubic expansion retains the quadratic word `N * x * N`. -/
theorem cube_add_sq_zero (x : A) {N : A} (hN : N * N = 0) :
    (x + N) ^ 3 =
      x ^ 3 + (x ^ 2 * N + x * N * x + N * x ^ 2) + N * x * N := by
  noncomm_ring [hN]

end NoncommutativeResidual

section NilpotentExponential

variable {A : Type*} [Ring A] [Module ℚ A]

/-- Mathlib's finite nilpotent exponential truncates exactly at degree one
on a square-zero operator. No analytic exponential is identified here. -/
theorem nilpotent_exp_eq_one_add {N : A} (hN : N * N = 0) :
    IsNilpotent.exp N = 1 + N := by
  rw [IsNilpotent.exp_eq_sum (show N ^ 2 = 0 by simpa only [pow_two] using hN)]
  simp [Finset.sum_range_succ]

end NilpotentExponential

end InfoGeometry.OperatorAlgebra.SquareZeroPolynomial
