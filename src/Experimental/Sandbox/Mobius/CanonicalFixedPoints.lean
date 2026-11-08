import Experimental.Sandbox.Mobius.CanonicalTransforms

namespace Experimental.Sandbox.Mobius

lemma translation_fixed_none (b : ℂ) :
    InfoGeometry.MobiusTransform.is_fixed_point (InfoGeometry.translation_transform b) none := by
  simp [InfoGeometry.MobiusTransform.is_fixed_point, translation_eval_none]

lemma translation_not_fixed_some_of_ne_zero (b z : ℂ) (hb : b ≠ 0) :
    ¬ InfoGeometry.MobiusTransform.is_fixed_point (InfoGeometry.translation_transform b) (some z) := by
  intro h
  unfold InfoGeometry.MobiusTransform.is_fixed_point at h
  rw [translation_eval_some] at h
  injection h with hz
  have hb0 : b = 0 := by
    exact add_left_cancel (show z + b = z + 0 by simpa using hz)
  exact hb hb0

lemma dilation_fixed_zero (a : ℂ) (ha : a ≠ 0) :
    InfoGeometry.MobiusTransform.is_fixed_point (InfoGeometry.dilation_transform a ha) (some 0) := by
  simp [InfoGeometry.MobiusTransform.is_fixed_point, dilation_eval_some]

lemma dilation_fixed_none (a : ℂ) (ha : a ≠ 0) :
    InfoGeometry.MobiusTransform.is_fixed_point (InfoGeometry.dilation_transform a ha) none := by
  simp [InfoGeometry.MobiusTransform.is_fixed_point, dilation_eval_none]

lemma inversion_fixed_one :
    InfoGeometry.MobiusTransform.is_fixed_point InfoGeometry.inversion_transform (some 1) := by
  simp [InfoGeometry.MobiusTransform.is_fixed_point, inversion_eval_some_of_ne_zero]

lemma inversion_fixed_neg_one :
    InfoGeometry.MobiusTransform.is_fixed_point InfoGeometry.inversion_transform (some (-1)) := by
  simp [InfoGeometry.MobiusTransform.is_fixed_point, inversion_eval_some_of_ne_zero]

lemma inversion_not_fixed_none :
    ¬ InfoGeometry.MobiusTransform.is_fixed_point InfoGeometry.inversion_transform none := by
  simp [InfoGeometry.MobiusTransform.is_fixed_point, inversion_eval_none]

lemma inversion_not_fixed_zero :
    ¬ InfoGeometry.MobiusTransform.is_fixed_point InfoGeometry.inversion_transform (some 0) := by
  simp [InfoGeometry.MobiusTransform.is_fixed_point, inversion_eval_zero]

end Experimental.Sandbox.Mobius
