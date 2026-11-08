/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.GeomSum

/-!
# Exact finite parametrix remainders in a noncommutative ring

The algebraic part of the random-walk expansion in Dimock, *The Renormalization
Group According to Balaban, I. Small Fields*, section 2.4, starts from
`H * P = 1 - K`. The approximation is `P` multiplied on the right by a finite
sum of powers of `K`. The product order is part of the theorem.

The native ring identity `mul_neg_geom_sum` supplies the geometric-series
cancellation. No pairwise commutativity, infinite sum, convergence, or
two-sided-inverse existence is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteParametrix

open Finset

variable {R : Type*} [Ring R]

/-- The ordered finite correction of the initial parametrix `P`. -/
def partialParametrix (P K : R) (N : ℕ) : R :=
  P * ∑ j ∈ range N, K ^ j

/-- Exact residual after `N` ordered corrections. -/
theorem mul_partialParametrix (H P K : R) (hHP : H * P = 1 - K) (N : ℕ) :
    H * partialParametrix P K N = 1 - K ^ N := by
  rw [partialParametrix, ← mul_assoc, hHP, mul_neg_geom_sum]

/-- Nilpotence gives a right inverse after finitely many corrections. -/
theorem mul_partialParametrix_eq_one (H P K : R) (hHP : H * P = 1 - K)
    (N : ℕ) (hK : K ^ N = 0) : H * partialParametrix P K N = 1 := by
  rw [mul_partialParametrix H P K hHP N, hK, sub_zero]

/-- A left inverse of `H` identifies the exact inverse remainder.

The single relation `G * H = 1` suffices; a right-inverse hypothesis is not
silently assumed or inferred for an arbitrary ring. -/
theorem inverse_remainder (H P K G : R) (hHP : H * P = 1 - K)
    (hGH : G * H = 1) (N : ℕ) :
    G - partialParametrix P K N = G * K ^ N := by
  have h := congrArg (fun X => G * X) (mul_partialParametrix H P K hHP N)
  rw [← mul_assoc, hGH, one_mul, mul_sub, mul_one] at h
  rw [h, sub_sub_cancel]

/-- With a left inverse already supplied, nilpotence makes the finite
parametrix equal that inverse. -/
theorem partialParametrix_eq_of_pow_eq_zero (H P K G : R)
    (hHP : H * P = 1 - K) (hGH : G * H = 1) (N : ℕ) (hK : K ^ N = 0) :
    partialParametrix P K N = G := by
  have h := inverse_remainder H P K G hHP hGH N
  rw [hK, mul_zero, sub_eq_zero] at h
  exact h.symm

end InfoGeometry.OperatorAlgebra.FiniteParametrix
