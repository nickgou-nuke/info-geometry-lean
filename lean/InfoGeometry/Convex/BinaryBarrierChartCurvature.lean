/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Convex.BinaryBarrierCoordinateHessian

/-!
# Curvature bounds in the actual binary log-odds chart

The transformed interval barrier is not globally standard self-concordant.
It does satisfy a global third-versus-second derivative bound. The standard
squared inequality holds exactly on the region described below. We retain
the owner's `trajectory 1 0` chart and actual iterated derivatives.
The polynomial readouts are cross-checked in
`scripts/check_binary_barrier_chart_curvature.py`; Lean is the proof authority.
-/

noncomputable section
namespace InfoGeometry.Convex.BinaryBarrierCoordinateHessian

open InfoGeometry.Convex.BipolarLogitBarrierDuality
open InfoGeometry.Analysis.LogOddsSimplexGeometry

/-- Global generalized self-concordance bound in the half-logit coordinate. -/
theorem barrier_chart_third_abs_lt_twice_second (ξ : ℝ) :
    |deriv (deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t)))) ξ| <
      2 * deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) ξ := by
  rw [barrier_chart_third_derivative, barrier_chart_second_derivative]
  have hp := trajectory_mem_Ioo 1 0 ξ
  have hpos : 0 < 16 * trajectory 1 0 ξ * (1 - trajectory 1 0 ξ) := by
    exact mul_pos (mul_pos (by norm_num) hp.1) (sub_pos.mpr hp.2)
  have ha : |1 - 2 * trajectory 1 0 ξ| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith [hp.1, hp.2]
  rw [abs_mul, abs_of_pos hpos]
  calc
    _ < (16 * trajectory 1 0 ξ * (1 - trajectory 1 0 ξ)) * 1 :=
      mul_lt_mul_of_pos_left ha hpos
    _ = _ := by ring

/-- Exact region for the standard squared self-concordance inequality. -/
theorem barrier_chart_standard_bound_iff (ξ : ℝ) :
    (deriv (deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t)))) ξ) ^ 2 ≤
        4 * (deriv (deriv (fun t => intervalBarrier (trajectory 1 0 t))) ξ) ^ 3 ↔
      1 ≤ 12 * trajectory 1 0 ξ * (1 - trajectory 1 0 ξ) := by
  rw [barrier_chart_third_derivative, barrier_chart_second_derivative]
  have hp := trajectory_mem_Ioo 1 0 ξ
  set p := trajectory 1 0 ξ
  have hpos : 0 < 256 * p ^ 2 * (1 - p) ^ 2 := by
    have h1 : 0 < p := hp.1
    have h2 : 0 < 1 - p := sub_pos.mpr hp.2
    positivity
  have hfactor : 4 * (8 * p * (1 - p)) ^ 3 -
      (16 * p * (1 - p) * (1 - 2 * p)) ^ 2 =
      (256 * p ^ 2 * (1 - p) ^ 2) * (12 * p * (1 - p) - 1) := by ring
  rw [← sub_nonneg, hfactor, mul_nonneg_iff_of_pos_left hpos, sub_nonneg]

end InfoGeometry.Convex.BinaryBarrierCoordinateHessian
