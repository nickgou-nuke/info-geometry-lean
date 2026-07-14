import InfoGeometry.Topology.MobiusGeometry

namespace InfoGeometry

/-- Translation acts by addition on finite points. -/
lemma canonical_translation_eval_some (b z : ℂ) :
    MobiusTransform.eval (translation_transform b) (some z) = some (z + b) := by
  simp [MobiusTransform.eval, translation_transform]

/-- Translation fixes infinity. -/
lemma canonical_translation_eval_none (b : ℂ) :
    MobiusTransform.eval (translation_transform b) none = none := by
  simp [MobiusTransform.eval, translation_transform]

/-- Dilation acts by multiplication on finite points. -/
lemma canonical_dilation_eval_some (a z : ℂ) (ha : a ≠ 0) :
    MobiusTransform.eval (dilation_transform a ha) (some z) = some (a * z) := by
  simp [MobiusTransform.eval, dilation_transform, ha]

/-- Dilation fixes infinity. -/
lemma canonical_dilation_eval_none (a : ℂ) (ha : a ≠ 0) :
    MobiusTransform.eval (dilation_transform a ha) none = none := by
  simp [MobiusTransform.eval, dilation_transform, ha]

/-- Inversion sends `0` to infinity. -/
lemma canonical_inversion_eval_zero :
    MobiusTransform.eval inversion_transform (some 0) = none := by
  simp [MobiusTransform.eval, inversion_transform]

/-- Inversion sends infinity to `0`. -/
lemma canonical_inversion_eval_none :
    MobiusTransform.eval inversion_transform none = some 0 := by
  simp [MobiusTransform.eval, inversion_transform]

/-- Nonzero translations have no finite fixed points. -/
lemma canonical_translation_not_fixed_some (b z : ℂ) (hb : b ≠ 0) :
    ¬ MobiusTransform.is_fixed_point (translation_transform b) (some z) := by
  intro h
  have hfixed := (fixed_point_translation (translation_transform b) (by rfl) (by rfl) hb) (some z)
  simpa [MobiusTransform.is_fixed_point] using hfixed.mp h

end InfoGeometry
