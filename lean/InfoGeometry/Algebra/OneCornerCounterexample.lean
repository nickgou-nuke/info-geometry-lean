/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A zero compressed corner does not imply full off-diagonality

In the full real `3 × 3` matrix algebra, a rank-one projection and the
involution swapping the first two coordinates while fixing the third satisfy
`P σ P = 0`. The complementary corner still has a unit diagonal entry.
-/

namespace InfoGeometry.Algebra.OneCornerCounterexample

open Matrix

/-- Projection onto the first coordinate. -/
def rankOneProjection : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- Swap the first two coordinates and fix the third. -/
def swapWithFixedAxis : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem rankOneProjection_idempotent :
    rankOneProjection * rankOneProjection = rankOneProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankOneProjection, Matrix.mul_apply, Fin.sum_univ_succ]

theorem swapWithFixedAxis_involution :
    swapWithFixedAxis * swapWithFixedAxis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapWithFixedAxis, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The projection and involution do not commute. -/
theorem rankOneProjection_swapWithFixedAxis_noncommute :
    rankOneProjection * swapWithFixedAxis ≠ swapWithFixedAxis * rankOneProjection := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [rankOneProjection, swapWithFixedAxis, Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem compressed_corner_zero :
    rankOneProjection * swapWithFixedAxis * rankOneProjection = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankOneProjection, swapWithFixedAxis, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The surviving third coordinate refutes the missing second-corner implication. -/
theorem complementary_corner_entry :
    ((1 - rankOneProjection) * swapWithFixedAxis * (1 - rankOneProjection)) 2 2 = 1 := by
  norm_num [rankOneProjection, swapWithFixedAxis, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply]
  decide

theorem complementary_corner_ne_zero :
    (1 - rankOneProjection) * swapWithFixedAxis * (1 - rankOneProjection) ≠ 0 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) h
  rw [complementary_corner_entry] at he
  exact one_ne_zero he

/-- Even with idempotence and an involution, a zero first corner does not
make the operator the sum of its two off-diagonal corners. -/
theorem swapWithFixedAxis_not_offDiagonal :
    swapWithFixedAxis ≠
      rankOneProjection * swapWithFixedAxis * (1 - rankOneProjection) +
        (1 - rankOneProjection) * swapWithFixedAxis * rankOneProjection := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) h
  norm_num [rankOneProjection, swapWithFixedAxis, Matrix.mul_apply, Fin.sum_univ_succ] at he

end InfoGeometry.Algebra.OneCornerCounterexample
