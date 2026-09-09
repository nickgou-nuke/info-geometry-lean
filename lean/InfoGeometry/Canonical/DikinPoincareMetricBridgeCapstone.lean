import InfoGeometry.Quantum.DikinPoincareMetricBridge

namespace InfoGeometry.Canonical.DikinPoincareMetricBridgeCapstone

open InfoGeometry.Quantum.DikinPoincareMetricBridge

/-! The finite Poincare pullback and Dikin rapidity normalization are
assembled from the native bridge lemmas. -/
theorem capstone_dikin_poincare_metric_bridge_synthesis (r tanh_chi : ℝ)
    (hr : r ^ 2 ≠ 1) (h : tanh_chi ^ 2 < 1) :
    (poincareMetricDensity r * (rapidityPullbackDerivative r) ^ 2 = 1) ∧
    (0 < dikinRapidityMetric tanh_chi) ∧
    (dikinRapidityMetric 0 = 2) := by
  exact ⟨poincare_pullback_isometry r hr,
    dikin_rapidity_metric_pos tanh_chi h,
    dikin_rapidity_metric_zero⟩

end InfoGeometry.Canonical.DikinPoincareMetricBridgeCapstone
