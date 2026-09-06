import InfoGeometry.Topology.MobiusGeometry
open InfoGeometry

lemma cross_ratio_translation (z1 z2 z3 z4 b : ℂ) :
    cross_ratio (z1 + b) (z2 + b) (z3 + b) (z4 + b) = cross_ratio z1 z2 z3 z4 := by
  unfold cross_ratio
  ring

lemma cross_ratio_scale (z1 z2 z3 z4 a : ℂ) (ha : a ≠ 0) :
    cross_ratio (a * z1) (a * z2) (a * z3) (a * z4) = cross_ratio z1 z2 z3 z4 := by
  unfold cross_ratio
  field_simp [ha]

lemma cross_ratio_affine (z1 z2 z3 z4 a b : ℂ) (ha : a ≠ 0) :
    cross_ratio (a * z1 + b) (a * z2 + b) (a * z3 + b) (a * z4 + b) = cross_ratio z1 z2 z3 z4 := by
  have htrans := cross_ratio_translation (a * z1) (a * z2) (a * z3) (a * z4) b
  have hscale := cross_ratio_scale z1 z2 z3 z4 a ha
  rw [htrans, hscale]
