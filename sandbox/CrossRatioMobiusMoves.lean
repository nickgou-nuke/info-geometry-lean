import InfoGeometry.Projective.CrossRatio

namespace InfoGeometry.Projective

lemma crossRatio_translation (z1 z2 z3 z4 b : ℂ) :
    crossRatio (z1 + b) (z2 + b) (z3 + b) (z4 + b) = crossRatio z1 z2 z3 z4 := by
  unfold crossRatio
  ring

lemma crossRatio_scale (z1 z2 z3 z4 a : ℂ) (ha : a ≠ 0) :
    crossRatio (a * z1) (a * z2) (a * z3) (a * z4) = crossRatio z1 z2 z3 z4 := by
  unfold crossRatio
  field_simp [ha]

lemma crossRatio_affine (z1 z2 z3 z4 a b : ℂ) (ha : a ≠ 0) :
    crossRatio (a * z1 + b) (a * z2 + b) (a * z3 + b) (a * z4 + b) = crossRatio z1 z2 z3 z4 := by
  have htrans := crossRatio_translation (z1 := a * z1) (z2 := a * z2) (z3 := a * z3) (z4 := a * z4) (b := b)
  have hscale := crossRatio_scale z1 z2 z3 z4 a ha
  simpa using htrans.trans hscale

lemma crossRatio_inversion (z1 z2 z3 z4 : ℂ)
    (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0) (hz4 : z4 ≠ 0) :
    crossRatio z1⁻¹ z2⁻¹ z3⁻¹ z4⁻¹ = crossRatio z1 z2 z3 z4 := by
  unfold crossRatio
  field_simp [hz1, hz2, hz3, hz4]
  ring

end InfoGeometry.Projective
