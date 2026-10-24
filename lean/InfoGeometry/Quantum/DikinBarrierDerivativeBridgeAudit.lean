/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.DikinBarrierDerivativeBridge

open InfoGeometry.Quantum.DikinApolloniusTrap

#print axioms dikin_barrier_eq_chart_sub_const
#print axioms dikin_barrier_hasDerivAt
#print axioms dikin_barrier_deriv_eq_chart_deriv
#print axioms dikin_barrier_second_derivative
#print axioms dikin_metric_derivative_abs_lt_twice
#print axioms dikin_standard_bound_iff
#print axioms InfoGeometry.Convex.BinaryBarrierCoordinateHessian.transformed_barrier_self_concordance_counterexample

example : deriv (deriv dikinScaleBarrier) 0 = 2 := by
  rw [dikin_barrier_second_derivative, dikin_scale_metric_at_zero]

example (ξ : ℝ) : 0 < deriv (deriv dikinScaleBarrier) ξ := by
  rw [dikin_barrier_second_derivative]
  exact dikin_scale_metric_pos ξ

example : deriv dikinScaleBarrier 0 = 0 := by
  simpa using (dikin_barrier_hasDerivAt 0).deriv
