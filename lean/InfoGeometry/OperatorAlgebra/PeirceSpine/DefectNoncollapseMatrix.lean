/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentDefectIteration
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# An algebraic Peirce metric with a nonvanishing defect orbit

In the full real matrix algebra `M₂(ℝ)`, the opposite corner seeds `E₁₂`
and `2 E₂₁` do not commute and generate `V = 2 I`. This algebraic metric
is a nonzero fixed point of `x ↦ x² - x`, so algebraicity does not imply
eventual vanishing of the defect orbit. Constancy is not independence of
the iterates, and no infinite-dimensional or spectral conclusion is claimed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceDefectNoncollapse

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceSpine

abbrev Op := Matrix (Fin 2) (Fin 2) ℝ

def cut : Op := !![1, 0; 0, 0]
def upper : Op := !![0, 1; 0, 0]
def lower : Op := !![0, 0; 2, 0]

theorem cut_idempotent : cut * cut = cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut, Matrix.mul_apply, Fin.sum_univ_two]

/-- Both seeds are actual elements of the corresponding Peirce corners. -/
theorem seed_corner_values : conePlus cut upper = upper ∧ coneMinus cut lower = lower := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [conePlus, coneMinus, cut, upper, lower,
      Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]

/-- The two boundary operators fail to commute in the full matrix ring. -/
theorem corner_products_noncommute :
    upper * lower ≠ lower * upper := by
  intro h
  have h00 := congrArg (fun M : Op => M 0 0) h
  norm_num [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem metric_value : genV cut upper lower = (2 : Op) := by
  unfold genV anticomm
  rw [seed_corner_values.1, seed_corner_values.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upper, lower, Matrix.mul_apply, Matrix.ofNat_apply, Fin.sum_univ_two]

/-- The metric is algebraic in the native Mathlib sense. -/
theorem metric_isAlgebraic : IsAlgebraic ℝ (genV cut upper lower) := by
  rw [metric_value]
  exact isAlgebraic_natCast 2

/-- The polynomial orbit is constant at the nonzero value `2 I`. -/
theorem metric_defect_iterates (n : ℕ) :
    idempotencyDefect^[n] (genV cut upper lower) = (2 : Op) := by
  rw [metric_value]
  apply Function.iterate_fixed
  norm_num [idempotencyDefect]

theorem metric_defect_iterates_ne_zero (n : ℕ) :
    idempotencyDefect^[n] (genV cut upper lower) ≠ 0 := by
  rw [metric_defect_iterates]
  intro h
  have h00 := congrArg (fun M : Op => M 0 0) h
  norm_num [Matrix.ofNat_apply] at h00

/-- An algebraic operator arising from noncommuting Peirce corners need not
have an eventually vanishing idempotency-defect orbit. -/
theorem algebraic_metric_without_eventual_vanishing :
    IsAlgebraic ℝ (genV cut upper lower) ∧
      ¬ ∃ n : ℕ, idempotencyDefect^[n] (genV cut upper lower) = 0 := by
  refine ⟨metric_isAlgebraic, ?_⟩
  rintro ⟨n, hn⟩
  exact metric_defect_iterates_ne_zero n hn

end InfoGeometry.OperatorAlgebra.PeirceDefectNoncollapse
