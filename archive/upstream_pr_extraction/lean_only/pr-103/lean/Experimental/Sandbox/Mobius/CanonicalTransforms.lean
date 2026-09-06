import Experimental.Sandbox.Mobius.EvalCases

namespace Experimental.Sandbox.Mobius

lemma translation_eval_some (b z : ℂ) :
    (InfoGeometry.translation_transform b).eval (some z) = some (z + b) := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.translation_transform]

lemma translation_eval_none (b : ℂ) :
    (InfoGeometry.translation_transform b).eval none = none := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.translation_transform]

lemma dilation_eval_some (a z : ℂ) (ha : a ≠ 0) :
    (InfoGeometry.dilation_transform a ha).eval (some z) = some (a * z) := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.dilation_transform]

lemma dilation_eval_none (a : ℂ) (ha : a ≠ 0) :
    (InfoGeometry.dilation_transform a ha).eval none = none := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.dilation_transform]

lemma inversion_eval_zero :
    InfoGeometry.inversion_transform.eval (some 0) = none := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.inversion_transform]

lemma inversion_eval_none :
    InfoGeometry.inversion_transform.eval none = some 0 := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.inversion_transform]

lemma inversion_eval_some_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    InfoGeometry.inversion_transform.eval (some z) = some z⁻¹ := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.inversion_transform, hz]

end Experimental.Sandbox.Mobius
