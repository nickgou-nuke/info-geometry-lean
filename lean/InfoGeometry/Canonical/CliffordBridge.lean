import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Canonical.GaugeUnified

namespace CliffordBridge

open InfoGeometry.Clifford

/-- Canonical naming for split quadratic-form agreement with gauge quadratic form. -/
theorem splitQuadratic_eq_gaugeQuadratic (v : ℝ × ℝ) :
    splitQ11 v = InfoGeometry.Canonical.Gauge.quad .split v := by
  simp [splitQ11_apply, InfoGeometry.Canonical.Gauge.quad]
  ring_nf

/-- Canonical naming for split bilinear-form agreement with gauge bilinear form. -/
theorem splitBilinear_eq_gaugeBilinear (u v : ℝ × ℝ) :
    splitB11 u v = InfoGeometry.Canonical.Gauge.bilinear .split u v := by
  rcases u with ⟨u1, u2⟩
  rcases v with ⟨v1, v2⟩
  simp [splitB11_apply, InfoGeometry.Canonical.Gauge.bilinear]

end CliffordBridge
