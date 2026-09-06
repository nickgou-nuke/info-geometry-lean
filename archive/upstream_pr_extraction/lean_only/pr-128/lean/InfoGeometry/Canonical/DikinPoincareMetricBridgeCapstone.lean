import InfoGeometry.Quantum.DikinPoincareMetricBridge

namespace InfoGeometry.Canonical.DikinPoincareMetricBridgeCapstone

open InfoGeometry.Quantum.DikinPoincareMetricBridge

theorem capstone_dikin_poincare_metric_bridge_synthesis (r tanh_chi : ℝ)
    (hr : r ^ 2 ≠ 1) (h : tanh_chi ^ 2 < 1) :
    (poincareMetricDensity r * (rapidityPullbackDerivative r) ^ 2 = 1) ∧
    (0 < dikinRapidityMetric tanh_chi) ∧
    (dikinRapidityMetric 0 = 2) :=
  grand_dikin_poincare_metric_bridge_synthesis r tanh_chi hr h

end InfoGeometry.Canonical.DikinPoincareMetricBridgeCapstone
