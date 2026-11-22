/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CornerCompressionTraceCounterexample
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cyclic trace observables for noncommutative matrix coefficients

For matrices over a noncommutative coefficient ring, the ordinary matrix trace
of a commutator need not vanish. Its class in the additive quotient by
commutators does vanish. Consequently the cyclic trace class of `U * F * V`
equals that of `F` whenever `V * U = 1`. This is a finite algebraic statement
on the full matrix operator algebra; it asserts no analytic Yang--Mills
existence, spectrum, or mass gap.
-/

namespace InfoGeometry.Canonical.OperatorYangMillsCyclicTrace

open InfoGeometry.Algebra.CyclicQuotient

variable {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The matrix trace is cyclic after passing to the additive cyclic quotient
of the coefficient ring, even when the coefficient ring is noncommutative. -/
theorem cyclicClass_trace_mul_comm (X Y : Matrix ι ι A) :
    cyclicClass ℤ A (Matrix.trace (X * Y)) =
      cyclicClass ℤ A (Matrix.trace (Y * X)) := by
  have h : Matrix.trace (X * Y - Y * X) =
      ∑ i, ∑ j, (X i j * Y j i - Y j i * X i j) := by
    rw [Matrix.trace_sub]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    conv_lhs =>
      arg 2
      rw [Finset.sum_comm]
    simp only [← Finset.sum_sub_distrib]
  have hzero : cyclicClass ℤ A
      (∑ i, ∑ j, (X i j * Y j i - Y j i * X i j)) = 0 := by
    simp only [map_sum, map_sub]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [← map_sub]
    change cyclicClass ℤ A (X i j * Y j i) -
        cyclicClass ℤ A (Y j i * X i j) = 0
    rw [cyclicClass_mul_comm]
    exact sub_self _
  have hclass := congrArg (cyclicClass ℤ A) h
  rw [Matrix.trace_sub, map_sub, hzero] at hclass
  exact sub_eq_zero.mp hclass

/-- Cyclic-quotient trace invariance under a matrix gauge transform. The only
inverse law needed is the displayed left-inverse equation `V * U = 1`. -/
theorem cyclicClass_trace_gauge_conjugate
    (U F V : Matrix ι ι A) (hVU : V * U = 1) :
    cyclicClass ℤ A (Matrix.trace (U * F * V)) =
      cyclicClass ℤ A (Matrix.trace F) := by
  have hcyc := cyclicClass_trace_mul_comm (U * F) V
  calc
    cyclicClass ℤ A (Matrix.trace (U * F * V)) =
        cyclicClass ℤ A (Matrix.trace (V * (U * F))) := by
          simpa only [Matrix.mul_assoc] using hcyc
    _ = cyclicClass ℤ A (Matrix.trace F) := by
          rw [← Matrix.mul_assoc, hVU, Matrix.one_mul]

end InfoGeometry.Canonical.OperatorYangMillsCyclicTrace
