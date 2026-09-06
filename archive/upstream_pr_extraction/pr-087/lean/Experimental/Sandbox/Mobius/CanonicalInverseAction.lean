import Experimental.Sandbox.Mobius.CanonicalTransforms

namespace Experimental.Sandbox.Mobius

lemma inv_translation_eval_some (b z : ℂ) :
    (InfoGeometry.inv (InfoGeometry.translation_transform b)).eval (some z) = some (z - b) := by
  simp [InfoGeometry.inv, InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]
  ring_nf

lemma inv_translation_eval_none (b : ℂ) :
    (InfoGeometry.inv (InfoGeometry.translation_transform b)).eval none = none := by
  simp [InfoGeometry.inv, InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]

lemma inv_dilation_eval_some (a z : ℂ) (ha : a ≠ 0) :
    (InfoGeometry.inv (InfoGeometry.dilation_transform a ha)).eval (some z) = some (z / a) := by
  simp [InfoGeometry.inv, InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval, ha]

lemma inv_dilation_eval_none (a : ℂ) (ha : a ≠ 0) :
    (InfoGeometry.inv (InfoGeometry.dilation_transform a ha)).eval none = none := by
  simp [InfoGeometry.inv, InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval]

lemma inv_inversion_eval_zero :
    (InfoGeometry.inv InfoGeometry.inversion_transform).eval (some 0) = none := by
  simp [InfoGeometry.inv, InfoGeometry.inversion_transform, InfoGeometry.MobiusTransform.eval]

lemma inv_inversion_eval_none :
    (InfoGeometry.inv InfoGeometry.inversion_transform).eval none = some 0 := by
  simp [InfoGeometry.inv, InfoGeometry.inversion_transform, InfoGeometry.MobiusTransform.eval]

lemma inv_inversion_eval_some_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    (InfoGeometry.inv InfoGeometry.inversion_transform).eval (some z) = some z⁻¹ := by
  simp [InfoGeometry.inv, InfoGeometry.inversion_transform, InfoGeometry.MobiusTransform.eval, hz]

lemma translation_eval_after_inv_translation (b z : ℂ) :
    (InfoGeometry.translation_transform b).eval
        ((InfoGeometry.inv (InfoGeometry.translation_transform b)).eval (some z)) = some z := by
  simpa using InfoGeometry.eval_inv (InfoGeometry.translation_transform b) (some z)

lemma inv_translation_eval_after_translation (b z : ℂ) :
    (InfoGeometry.inv (InfoGeometry.translation_transform b)).eval
        ((InfoGeometry.translation_transform b).eval (some z)) = some z := by
  simpa using InfoGeometry.eval_inv_left (InfoGeometry.translation_transform b) (some z)

lemma dilation_eval_after_inv_dilation (a z : ℂ) (ha : a ≠ 0) :
    (InfoGeometry.dilation_transform a ha).eval
        ((InfoGeometry.inv (InfoGeometry.dilation_transform a ha)).eval (some z)) = some z := by
  simpa using InfoGeometry.eval_inv (InfoGeometry.dilation_transform a ha) (some z)

lemma inv_dilation_eval_after_dilation (a z : ℂ) (ha : a ≠ 0) :
    (InfoGeometry.inv (InfoGeometry.dilation_transform a ha)).eval
        ((InfoGeometry.dilation_transform a ha).eval (some z)) = some z := by
  simpa using InfoGeometry.eval_inv_left (InfoGeometry.dilation_transform a ha) (some z)

end Experimental.Sandbox.Mobius
