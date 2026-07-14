import InfoGeometry.Topology.MobiusGeometry

namespace InfoGeometry

lemma translation_transform_eval_some (b z : ℂ) :
    MobiusTransform.eval (translation_transform b) (some z) = some (z + b) := by
  simp [MobiusTransform.eval, translation_transform]

lemma translation_transform_eval_none (b : ℂ) :
    MobiusTransform.eval (translation_transform b) none = none := by
  simp [MobiusTransform.eval, translation_transform]

lemma inversion_transform_eval_zero :
    MobiusTransform.eval inversion_transform (some 0) = none := by
  simp [MobiusTransform.eval, inversion_transform]

lemma inversion_transform_eval_none :
    MobiusTransform.eval inversion_transform none = some 0 := by
  simp [MobiusTransform.eval, inversion_transform]

lemma translation_fixed_points (b : ℂ) (hb : b ≠ 0) :
    ∀ z, MobiusTransform.is_fixed_point (translation_transform b) z ↔ z = none := by
  simpa [MobiusTransform.is_fixed_point, translation_transform] using
    (fixed_point_translation (translation_transform b) (by rfl) (by rfl) hb)

lemma translation_fixed_points_some (b z : ℂ) (hb : b ≠ 0) :
    ¬ MobiusTransform.is_fixed_point (translation_transform b) (some z) := by
  intro h
  have hnone := (translation_fixed_points b hb (some z)).mp h
  cases hnone

end InfoGeometry
