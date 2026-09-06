import Experimental.Sandbox.Mobius.EvalBijective

namespace Experimental.Sandbox.Mobius

noncomputable def mobiusEvalEquiv (M : InfoGeometry.MobiusTransform) :
    InfoGeometry.RiemannSphere ≃ InfoGeometry.RiemannSphere where
  toFun := M.eval
  invFun := (InfoGeometry.inv M).eval
  left_inv := by
    intro z
    exact InfoGeometry.eval_inv_left M z
  right_inv := by
    intro z
    exact InfoGeometry.eval_inv M z

lemma mobiusEvalEquiv_apply (M : InfoGeometry.MobiusTransform)
    (z : InfoGeometry.RiemannSphere) :
    mobiusEvalEquiv M z = M.eval z := rfl

lemma mobiusEvalEquiv_symm_apply (M : InfoGeometry.MobiusTransform)
    (z : InfoGeometry.RiemannSphere) :
    (mobiusEvalEquiv M).symm z = (InfoGeometry.inv M).eval z := rfl

lemma mobiusEvalEquiv_apply_symm_apply (M : InfoGeometry.MobiusTransform)
    (z : InfoGeometry.RiemannSphere) :
    mobiusEvalEquiv M ((mobiusEvalEquiv M).symm z) = z := by
  exact (mobiusEvalEquiv M).apply_symm_apply z

lemma mobiusEvalEquiv_symm_apply_apply (M : InfoGeometry.MobiusTransform)
    (z : InfoGeometry.RiemannSphere) :
    (mobiusEvalEquiv M).symm (mobiusEvalEquiv M z) = z := by
  exact (mobiusEvalEquiv M).symm_apply_apply z

lemma mobiusEvalEquiv_injective (M : InfoGeometry.MobiusTransform) :
    Function.Injective (mobiusEvalEquiv M) := by
  exact (mobiusEvalEquiv M).injective

lemma mobiusEvalEquiv_surjective (M : InfoGeometry.MobiusTransform) :
    Function.Surjective (mobiusEvalEquiv M) := by
  exact (mobiusEvalEquiv M).surjective

end Experimental.Sandbox.Mobius
