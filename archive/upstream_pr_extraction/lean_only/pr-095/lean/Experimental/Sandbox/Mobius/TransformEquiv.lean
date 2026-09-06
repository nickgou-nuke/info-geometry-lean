import Experimental.Sandbox.Mobius.EvalEquivIdentity

namespace Experimental.Sandbox.Mobius

lemma mobiusTransform_equiv_refl (M : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv M M := by
  intro z
  rfl

lemma mobiusTransform_equiv_symm {M N : InfoGeometry.MobiusTransform}
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    InfoGeometry.MobiusTransform.equiv N M := by
  intro z
  exact (h z).symm

lemma mobiusTransform_equiv_trans {M N P : InfoGeometry.MobiusTransform}
    (hMN : InfoGeometry.MobiusTransform.equiv M N)
    (hNP : InfoGeometry.MobiusTransform.equiv N P) :
    InfoGeometry.MobiusTransform.equiv M P := by
  intro z
  exact (hMN z).trans (hNP z)

lemma mobiusEvalEquiv_eq_of_mobiusTransform_equiv
    {M N : InfoGeometry.MobiusTransform}
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    mobiusEvalEquiv M = mobiusEvalEquiv N := by
  ext z
  exact h z

lemma mobiusTransform_equiv_of_mobiusEvalEquiv_eq
    {M N : InfoGeometry.MobiusTransform}
    (h : mobiusEvalEquiv M = mobiusEvalEquiv N) :
    InfoGeometry.MobiusTransform.equiv M N := by
  intro z
  exact congrFun (congrArg DFunLike.coe h) z

lemma mobiusTransform_equiv_iff_mobiusEvalEquiv_eq
    (M N : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv M N ↔ mobiusEvalEquiv M = mobiusEvalEquiv N := by
  constructor
  · exact mobiusEvalEquiv_eq_of_mobiusTransform_equiv
  · exact mobiusTransform_equiv_of_mobiusEvalEquiv_eq

lemma mobiusTransform_equiv_translation_zero_dilation_one :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.translation_transform 0)
      (InfoGeometry.dilation_transform 1 one_ne_zero) := by
  apply mobiusTransform_equiv_of_mobiusEvalEquiv_eq
  rw [mobiusEvalEquiv_translation_zero, mobiusEvalEquiv_dilation_one]

end Experimental.Sandbox.Mobius
