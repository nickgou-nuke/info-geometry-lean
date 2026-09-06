import Experimental.Sandbox.Mobius.TransformEquiv

namespace Experimental.Sandbox.Mobius

lemma mobiusTransform_equiv_comp_left
    (L : InfoGeometry.MobiusTransform) {M N : InfoGeometry.MobiusTransform}
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    InfoGeometry.MobiusTransform.equiv (InfoGeometry.comp L M) (InfoGeometry.comp L N) := by
  intro z
  rw [InfoGeometry.eval_comp, InfoGeometry.eval_comp, h z]

lemma mobiusTransform_equiv_comp_right
    {M N : InfoGeometry.MobiusTransform} (R : InfoGeometry.MobiusTransform)
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    InfoGeometry.MobiusTransform.equiv (InfoGeometry.comp M R) (InfoGeometry.comp N R) := by
  intro z
  rw [InfoGeometry.eval_comp, InfoGeometry.eval_comp]
  exact h (R.eval z)

lemma mobiusTransform_equiv_comp_congr
    {M₁ N₁ M₂ N₂ : InfoGeometry.MobiusTransform}
    (h₁ : InfoGeometry.MobiusTransform.equiv M₁ N₁)
    (h₂ : InfoGeometry.MobiusTransform.equiv M₂ N₂) :
    InfoGeometry.MobiusTransform.equiv
      (InfoGeometry.comp M₁ M₂) (InfoGeometry.comp N₁ N₂) := by
  exact mobiusTransform_equiv_trans
    (mobiusTransform_equiv_comp_right M₂ h₁)
    (mobiusTransform_equiv_comp_left N₁ h₂)

lemma mobiusTransform_equiv_inv
    {M N : InfoGeometry.MobiusTransform}
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    InfoGeometry.MobiusTransform.equiv (InfoGeometry.inv M) (InfoGeometry.inv N) := by
  apply mobiusTransform_equiv_of_mobiusEvalEquiv_eq
  calc
    mobiusEvalEquiv (InfoGeometry.inv M) = (mobiusEvalEquiv M).symm :=
      (mobiusEvalEquiv_symm_eq_inv M).symm
    _ = (mobiusEvalEquiv N).symm := by
      rw [mobiusEvalEquiv_eq_of_mobiusTransform_equiv h]
    _ = mobiusEvalEquiv (InfoGeometry.inv N) :=
      mobiusEvalEquiv_symm_eq_inv N

lemma mobiusTransform_equiv_inv_iff
    (M N : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv (InfoGeometry.inv M) (InfoGeometry.inv N) ↔
      InfoGeometry.MobiusTransform.equiv M N := by
  constructor
  · intro h
    have hinv := mobiusTransform_equiv_inv h
    simpa [InfoGeometry.inv] using hinv
  · exact mobiusTransform_equiv_inv

end Experimental.Sandbox.Mobius
