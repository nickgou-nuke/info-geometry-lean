import InfoGeometry.Projective.CrossRatio

namespace InfoGeometry.Projective.CrossRatioSandbox

lemma crossRatio_translation (z1 z2 z3 z4 b : ℂ) :
    InfoGeometry.Projective.crossRatio (z1 + b) (z2 + b) (z3 + b) (z4 + b) =
      InfoGeometry.Projective.crossRatio z1 z2 z3 z4 := by
  unfold InfoGeometry.Projective.crossRatio
  ring

lemma crossRatio_scale (z1 z2 z3 z4 a : ℂ) (ha : a ≠ 0) :
    InfoGeometry.Projective.crossRatio (a * z1) (a * z2) (a * z3) (a * z4) =
      InfoGeometry.Projective.crossRatio z1 z2 z3 z4 := by
  unfold InfoGeometry.Projective.crossRatio
  field_simp [ha]

lemma crossRatio_affine (z1 z2 z3 z4 a b : ℂ) (ha : a ≠ 0) :
    InfoGeometry.Projective.crossRatio (a * z1 + b) (a * z2 + b) (a * z3 + b) (a * z4 + b) =
      InfoGeometry.Projective.crossRatio z1 z2 z3 z4 := by
  have htrans := crossRatio_translation (z1 := a * z1) (z2 := a * z2) (z3 := a * z3) (z4 := a * z4) (b := b)
  have hscale := crossRatio_scale z1 z2 z3 z4 a ha
  simpa using htrans.trans hscale

lemma crossRatio_inversion (z1 z2 z3 z4 : ℂ)
    (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0) (hz4 : z4 ≠ 0) :
    InfoGeometry.Projective.crossRatio z1⁻¹ z2⁻¹ z3⁻¹ z4⁻¹ =
      InfoGeometry.Projective.crossRatio z1 z2 z3 z4 := by
  unfold InfoGeometry.Projective.crossRatio
  field_simp [hz1, hz2, hz3, hz4]
  ring

lemma crossRatio_affine_inversion (z1 z2 z3 z4 a b : ℂ)
    (ha : a ≠ 0)
    (h1 : a * z1 + b ≠ 0) (h2 : a * z2 + b ≠ 0)
    (h3 : a * z3 + b ≠ 0) (h4 : a * z4 + b ≠ 0) :
    InfoGeometry.Projective.crossRatio
        (a * z1 + b)⁻¹ (a * z2 + b)⁻¹ (a * z3 + b)⁻¹ (a * z4 + b)⁻¹ =
      InfoGeometry.Projective.crossRatio z1 z2 z3 z4 := by
  have hinv := crossRatio_inversion (a * z1 + b) (a * z2 + b) (a * z3 + b) (a * z4 + b) h1 h2 h3 h4
  have haff := crossRatio_affine z1 z2 z3 z4 a b ha
  exact hinv.trans haff

end InfoGeometry.Projective.CrossRatioSandbox
