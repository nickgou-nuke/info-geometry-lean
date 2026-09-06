import Experimental.Sandbox.Mobius.TransformEquivComposition

namespace Experimental.Sandbox.Mobius

lemma mobiusTransform_equiv_comp_translation_zero_left
    (M : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp (InfoGeometry.translation_transform 0) M) M := by
  intro z
  rw [InfoGeometry.eval_comp]
  cases M.eval z with
  | none => simp [InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]
  | some w => simp [InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]

lemma mobiusTransform_equiv_comp_translation_zero_right
    (M : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp M (InfoGeometry.translation_transform 0)) M := by
  intro z
  rw [InfoGeometry.eval_comp]
  cases z with
  | none => simp [InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]
  | some w => simp [InfoGeometry.translation_transform, InfoGeometry.MobiusTransform.eval]

lemma mobiusTransform_equiv_comp_dilation_one_left
    (M : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp (InfoGeometry.dilation_transform 1 one_ne_zero) M) M := by
  intro z
  rw [InfoGeometry.eval_comp]
  cases M.eval z with
  | none => simp [InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval]
  | some w => simp [InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval]

lemma mobiusTransform_equiv_comp_dilation_one_right
    (M : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp M (InfoGeometry.dilation_transform 1 one_ne_zero)) M := by
  intro z
  rw [InfoGeometry.eval_comp]
  cases z with
  | none => simp [InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval]
  | some w => simp [InfoGeometry.dilation_transform, InfoGeometry.MobiusTransform.eval]

lemma mobiusTransform_equiv_translation_zero_left_iff
    (M N : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp (InfoGeometry.translation_transform 0) M) N ↔
      InfoGeometry.MobiusTransform.equiv M N := by
  constructor
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_symm (mobiusTransform_equiv_comp_translation_zero_left M)) h
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_comp_translation_zero_left M) h

lemma mobiusTransform_equiv_translation_zero_right_iff
    (M N : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp M (InfoGeometry.translation_transform 0)) N ↔
      InfoGeometry.MobiusTransform.equiv M N := by
  constructor
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_symm (mobiusTransform_equiv_comp_translation_zero_right M)) h
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_comp_translation_zero_right M) h

lemma mobiusTransform_equiv_dilation_one_left_iff
    (M N : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp (InfoGeometry.dilation_transform 1 one_ne_zero) M) N ↔
      InfoGeometry.MobiusTransform.equiv M N := by
  constructor
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_symm (mobiusTransform_equiv_comp_dilation_one_left M)) h
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_comp_dilation_one_left M) h

lemma mobiusTransform_equiv_dilation_one_right_iff
    (M N : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp M (InfoGeometry.dilation_transform 1 one_ne_zero)) N ↔
      InfoGeometry.MobiusTransform.equiv M N := by
  constructor
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_symm (mobiusTransform_equiv_comp_dilation_one_right M)) h
  · intro h
    exact mobiusTransform_equiv_trans
      (mobiusTransform_equiv_comp_dilation_one_right M) h

end Experimental.Sandbox.Mobius
