import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Research.GaugeUnified

namespace InfoGeometry.Research.CliffordBridge

open InfoGeometry.Clifford

theorem q_agrees_with_Gauge_quad (v : ℝ × ℝ) :
    splitQ11 v = InfoGeometry.Research.Gauge.quad .split v := by
  simp [splitQ11_apply, InfoGeometry.Research.Gauge.quad]
  ring

theorem B_agrees_with_Gauge_bilinear (u v : ℝ × ℝ) :
    splitB11 u v = InfoGeometry.Research.Gauge.bilinear .split u v := by
  rfl

end InfoGeometry.Research.CliffordBridge
