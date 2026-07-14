import InfoGeometry.Projective.CrossRatio

namespace InfoGeometry.Projective.CrossRatioSandbox

lemma fractionalLinear_sub
    (z w a b c d : ℂ)
    (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    (a * z + b) / (c * z + d) - (a * w + b) / (c * w + d) =
      (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
  have hzc : z * c + d ≠ 0 := by simpa [mul_comm] using hz
  have hwc : w * c + d ≠ 0 := by simpa [mul_comm] using hw
  field_simp [hz, hw, hzc, hwc]
  ring

lemma crossRatio_fractionalLinear_finite
    (z1 z2 z3 z4 a b c d : ℂ)
    (hdet : a * d - b * c ≠ 0)
    (h1 : c * z1 + d ≠ 0) (h2 : c * z2 + d ≠ 0)
    (h3 : c * z3 + d ≠ 0) (h4 : c * z4 + d ≠ 0) :
    InfoGeometry.Projective.crossRatio
        ((a * z1 + b) / (c * z1 + d))
        ((a * z2 + b) / (c * z2 + d))
        ((a * z3 + b) / (c * z3 + d))
        ((a * z4 + b) / (c * z4 + d)) =
      InfoGeometry.Projective.crossRatio z1 z2 z3 z4 := by
  unfold InfoGeometry.Projective.crossRatio
  rw [fractionalLinear_sub z1 z2 a b c d h1 h2]
  rw [fractionalLinear_sub z3 z4 a b c d h3 h4]
  rw [fractionalLinear_sub z1 z3 a b c d h1 h3]
  rw [fractionalLinear_sub z2 z4 a b c d h2 h4]
  field_simp [hdet, h1, h2, h3, h4]

end InfoGeometry.Projective.CrossRatioSandbox
