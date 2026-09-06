import Experimental.Sandbox.Mobius.EvalEquivComposition

namespace Experimental.Sandbox.Mobius

lemma mobiusEvalEquiv_symm_eq_inv
    (M : InfoGeometry.MobiusTransform) :
    (mobiusEvalEquiv M).symm = mobiusEvalEquiv (InfoGeometry.inv M) := by
  ext z
  rfl

lemma mobiusEvalEquiv_inv_symm_eq
    (M : InfoGeometry.MobiusTransform) :
    (mobiusEvalEquiv (InfoGeometry.inv M)).symm = mobiusEvalEquiv M := by
  ext z
  simp [mobiusEvalEquiv, InfoGeometry.inv]

lemma mobiusEvalEquiv_inv_apply
    (M : InfoGeometry.MobiusTransform) (z : InfoGeometry.RiemannSphere) :
    mobiusEvalEquiv (InfoGeometry.inv M) z = (InfoGeometry.inv M).eval z := rfl

lemma mobiusEvalEquiv_inv_symm_apply
    (M : InfoGeometry.MobiusTransform) (z : InfoGeometry.RiemannSphere) :
    (mobiusEvalEquiv (InfoGeometry.inv M)).symm z = M.eval z := by
  rw [mobiusEvalEquiv_inv_symm_eq]
  rfl

lemma mobiusEvalEquiv_symm_trans_self
    (M : InfoGeometry.MobiusTransform) :
    (mobiusEvalEquiv M).symm.trans (mobiusEvalEquiv M) = Equiv.refl InfoGeometry.RiemannSphere := by
  ext z
  exact (mobiusEvalEquiv M).apply_symm_apply z

lemma mobiusEvalEquiv_trans_symm_self
    (M : InfoGeometry.MobiusTransform) :
    (mobiusEvalEquiv M).trans (mobiusEvalEquiv M).symm = Equiv.refl InfoGeometry.RiemannSphere := by
  ext z
  exact (mobiusEvalEquiv M).symm_apply_apply z

end Experimental.Sandbox.Mobius
