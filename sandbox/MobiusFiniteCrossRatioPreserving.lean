import InfoGeometry.Topology.MobiusGeometry

namespace InfoGeometry.MobiusCrossRatioSandbox

lemma fractionalLinear_sub
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (hz : M.c * z + M.d ≠ 0) (hw : M.c * w + M.d ≠ 0) :
    (M.a * z + M.b) / (M.c * z + M.d) - (M.a * w + M.b) / (M.c * w + M.d) =
      (M.a * M.d - M.b * M.c) * (z - w) /
        ((M.c * z + M.d) * (M.c * w + M.d)) := by
  have hzc : z * M.c + M.d ≠ 0 := by simpa [mul_comm] using hz
  have hwc : w * M.c + M.d ≠ 0 := by simpa [mul_comm] using hw
  field_simp [hz, hw, hzc, hwc]
  ring

lemma cross_ratio_fractionalLinear_finite
    (M : InfoGeometry.MobiusTransform) (z1 z2 z3 z4 : ℂ)
    (h1 : M.c * z1 + M.d ≠ 0) (h2 : M.c * z2 + M.d ≠ 0)
    (h3 : M.c * z3 + M.d ≠ 0) (h4 : M.c * z4 + M.d ≠ 0) :
    InfoGeometry.cross_ratio
        ((M.a * z1 + M.b) / (M.c * z1 + M.d))
        ((M.a * z2 + M.b) / (M.c * z2 + M.d))
        ((M.a * z3 + M.b) / (M.c * z3 + M.d))
        ((M.a * z4 + M.b) / (M.c * z4 + M.d)) =
      InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  unfold InfoGeometry.cross_ratio
  rw [fractionalLinear_sub M z1 z3 h1 h3]
  rw [fractionalLinear_sub M z2 z4 h2 h4]
  rw [fractionalLinear_sub M z2 z3 h2 h3]
  rw [fractionalLinear_sub M z1 z4 h1 h4]
  field_simp [M.det_ne_zero, h1, h2, h3, h4]

lemma eval_some_eq_fractional
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hz : M.c * z + M.d ≠ 0) :
    M.eval (some z) = some ((M.a * z + M.b) / (M.c * z + M.d)) := by
  simp [InfoGeometry.MobiusTransform.eval, hz]

end InfoGeometry.MobiusCrossRatioSandbox
