import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Research.GaugeUnified

namespace InfoGeometry.Research.CliffordBridge

open InfoGeometry.Clifford

theorem q_agrees_with_Gauge_quad (v : ℝ × ℝ) :
    splitQ11 v = InfoGeometry.Research.Gauge.quad .split v := by
  simp [splitQ11_apply, InfoGeometry.Research.Gauge.quad]
  ring

/-- Canonical naming for split quadratic-form agreement with gauge quadratic form. -/
theorem splitQuadratic_eq_gaugeQuadratic (v : ℝ × ℝ) :
    splitQ11 v = InfoGeometry.Research.Gauge.quad .split v :=
  q_agrees_with_Gauge_quad v

theorem B_agrees_with_Gauge_bilinear (u v : ℝ × ℝ) :
    splitB11 u v = InfoGeometry.Research.Gauge.bilinear .split u v := by
  rfl

/-- Canonical naming for split bilinear-form agreement with gauge bilinear form. -/
theorem splitBilinear_eq_gaugeBilinear (u v : ℝ × ℝ) :
    splitB11 u v = InfoGeometry.Research.Gauge.bilinear .split u v :=
  B_agrees_with_Gauge_bilinear u v

attribute [deprecated splitQuadratic_eq_gaugeQuadratic (since := "2026-02-26")]
  q_agrees_with_Gauge_quad
attribute [deprecated splitBilinear_eq_gaugeBilinear (since := "2026-02-26")]
  B_agrees_with_Gauge_bilinear

end InfoGeometry.Research.CliffordBridge
