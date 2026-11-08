/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.DikinApolloniusTrap
import InfoGeometry.Convex.BinaryBarrierChartCurvature

/-! # Actual derivatives of the Dikin scale potential

The additive constant relating the two existing potentials transports the
correct curvature bounds without claiming global standard self-concordance.
-/

noncomputable section
namespace InfoGeometry.Quantum.DikinApolloniusTrap

open InfoGeometry.Convex.BipolarLogitBarrierDuality
open InfoGeometry.Convex.BinaryBarrierCoordinateHessian
open InfoGeometry.Analysis.LogOddsSimplexGeometry

theorem dikin_barrier_eq_chart_sub_const (ξ : ℝ) :
    dikinScaleBarrier ξ = intervalBarrier (trajectory 1 0 ξ) - Real.log 4 := by
  rw [dikin_barrier_eq_two_log_cosh, interval_barrier_log_cosh]
  ring

theorem dikin_barrier_hasDerivAt (ξ : ℝ) :
    HasDerivAt dikinScaleBarrier (2 * Real.tanh ξ) ξ := by
  have h := ((Real.hasDerivAt_cosh ξ).log (Real.cosh_pos ξ).ne').const_mul 2
  convert h using 1
  · funext t
    exact dikin_barrier_eq_two_log_cosh t
  · rw [Real.tanh_eq_sinh_div_cosh]

theorem dikin_barrier_deriv_eq_chart_deriv :
    deriv dikinScaleBarrier = deriv (fun t => intervalBarrier (trajectory 1 0 t)) := by
  funext ξ
  have h := (barrier_chart_hasDerivAt ξ).sub_const (Real.log 4)
  have hf : dikinScaleBarrier = fun t => intervalBarrier (trajectory 1 0 t) - Real.log 4 :=
    funext dikin_barrier_eq_chart_sub_const
  rw [hf, h.deriv, (barrier_chart_hasDerivAt ξ).deriv]

/-- The defined metric is the Hessian of this scalar potential in this coordinate. -/
theorem dikin_barrier_second_derivative (ξ : ℝ) :
    deriv (deriv dikinScaleBarrier) ξ = dikinScaleMetric ξ := by
  have hfirst : 2 * Real.tanh ξ = 4 * trajectory 1 0 ξ - 2 := by
    rw [← (dikin_barrier_hasDerivAt ξ).deriv, dikin_barrier_deriv_eq_chart_deriv,
      (barrier_chart_hasDerivAt ξ).deriv]
  rw [dikin_barrier_deriv_eq_chart_deriv, barrier_chart_second_derivative]
  unfold dikinScaleMetric
  have ht : Real.tanh ξ = 2 * trajectory 1 0 ξ - 1 := by linarith
  rw [ht]
  ring

/-- Global generalized curvature control, using the actual derivative of the metric. -/
theorem dikin_metric_derivative_abs_lt_twice (ξ : ℝ) :
    |deriv dikinScaleMetric ξ| < 2 * dikinScaleMetric ξ := by
  have hf : dikinScaleMetric = deriv (deriv dikinScaleBarrier) :=
    (funext dikin_barrier_second_derivative).symm
  rw [hf, dikin_barrier_deriv_eq_chart_deriv]
  exact barrier_chart_third_abs_lt_twice_second ξ

/-- Exact standard squared self-concordance region; it is not the whole real line. -/
theorem dikin_standard_bound_iff (ξ : ℝ) :
    (deriv dikinScaleMetric ξ) ^ 2 ≤ 4 * (dikinScaleMetric ξ) ^ 3 ↔
      1 ≤ 12 * trajectory 1 0 ξ * (1 - trajectory 1 0 ξ) := by
  have hf : dikinScaleMetric = deriv (deriv dikinScaleBarrier) :=
    (funext dikin_barrier_second_derivative).symm
  rw [hf, dikin_barrier_deriv_eq_chart_deriv]
  exact barrier_chart_standard_bound_iff ξ

end InfoGeometry.Quantum.DikinApolloniusTrap
