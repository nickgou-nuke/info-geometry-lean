import Experimental.Sandbox.Mobius.EvalEquivInverse

namespace Experimental.Sandbox.Mobius

lemma mobiusEvalEquiv_translation_zero_apply
    (z : InfoGeometry.RiemannSphere) :
    mobiusEvalEquiv (InfoGeometry.translation_transform 0) z = z := by
  cases z with
  | none => simp [mobiusEvalEquiv, InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]
  | some z => simp [mobiusEvalEquiv, InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]

lemma mobiusEvalEquiv_translation_zero :
    mobiusEvalEquiv (InfoGeometry.translation_transform 0) =
      Equiv.refl InfoGeometry.RiemannSphere := by
  ext z
  exact mobiusEvalEquiv_translation_zero_apply z

lemma mobiusEvalEquiv_dilation_one_apply
    (z : InfoGeometry.RiemannSphere) :
    mobiusEvalEquiv (InfoGeometry.dilation_transform 1 one_ne_zero) z = z := by
  cases z with
  | none => simp [mobiusEvalEquiv, InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval]
  | some z => simp [mobiusEvalEquiv, InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval]

lemma mobiusEvalEquiv_dilation_one :
    mobiusEvalEquiv (InfoGeometry.dilation_transform 1 one_ne_zero) =
      Equiv.refl InfoGeometry.RiemannSphere := by
  ext z
  exact mobiusEvalEquiv_dilation_one_apply z

lemma mobiusEvalEquiv_translation_zero_symm :
    (mobiusEvalEquiv (InfoGeometry.translation_transform 0)).symm =
      Equiv.refl InfoGeometry.RiemannSphere := by
  rw [mobiusEvalEquiv_translation_zero]
  rfl

lemma mobiusEvalEquiv_dilation_one_symm :
    (mobiusEvalEquiv (InfoGeometry.dilation_transform 1 one_ne_zero)).symm =
      Equiv.refl InfoGeometry.RiemannSphere := by
  rw [mobiusEvalEquiv_dilation_one]
  rfl

end Experimental.Sandbox.Mobius
