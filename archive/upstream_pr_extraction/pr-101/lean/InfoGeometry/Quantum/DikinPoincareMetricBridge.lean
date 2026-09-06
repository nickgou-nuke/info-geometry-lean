import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.DikinPoincareMetricBridge

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def poincareMetricDensity (r : ℝ) : ℝ :=
  4 / (1 - r ^ 2) ^ 2

def rapidityPullbackDerivative (r : ℝ) : ℝ :=
  (1 - r ^ 2) / 2

theorem poincare_pullback_isometry (r : ℝ) (hr : r ^ 2 ≠ 1) :
    poincareMetricDensity r * (rapidityPullbackDerivative r) ^ 2 = 1 := by
  unfold poincareMetricDensity rapidityPullbackDerivative
  have h_sub : 1 - r ^ 2 ≠ 0 := by intro h; apply hr; linarith
  have h_sub2 : (1 - r ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h_sub
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  field_simp
  ring

def dikinRapidityMetric (tanh_chi : ℝ) : ℝ :=
  2 * (1 - tanh_chi ^ 2)

theorem dikin_rapidity_metric_pos (tanh_chi : ℝ) (h : tanh_chi ^ 2 < 1) :
    0 < dikinRapidityMetric tanh_chi := by
  unfold dikinRapidityMetric
  nlinarith

theorem dikin_rapidity_metric_zero :
    dikinRapidityMetric 0 = 2 := by
  unfold dikinRapidityMetric
  ring

theorem grand_dikin_poincare_metric_bridge_synthesis (r tanh_chi : ℝ)
    (hr : r ^ 2 ≠ 1) (h : tanh_chi ^ 2 < 1) :
    (poincareMetricDensity r * (rapidityPullbackDerivative r) ^ 2 = 1) ∧
    (0 < dikinRapidityMetric tanh_chi) ∧
    (dikinRapidityMetric 0 = 2) :=
  ⟨poincare_pullback_isometry r hr,
   dikin_rapidity_metric_pos tanh_chi h,
   dikin_rapidity_metric_zero⟩
