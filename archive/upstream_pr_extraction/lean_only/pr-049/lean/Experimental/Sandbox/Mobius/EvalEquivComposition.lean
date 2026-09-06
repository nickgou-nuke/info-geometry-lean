import Experimental.Sandbox.Mobius.EvalEquiv

namespace Experimental.Sandbox.Mobius

lemma mobiusEvalEquiv_comp_apply
    (M1 M2 : InfoGeometry.MobiusTransform) (z : InfoGeometry.RiemannSphere) :
    mobiusEvalEquiv (InfoGeometry.comp M1 M2) z =
      ((mobiusEvalEquiv M2).trans (mobiusEvalEquiv M1)) z := by
  simp [mobiusEvalEquiv, InfoGeometry.eval_comp]

lemma mobiusEvalEquiv_comp
    (M1 M2 : InfoGeometry.MobiusTransform) :
    mobiusEvalEquiv (InfoGeometry.comp M1 M2) =
      (mobiusEvalEquiv M2).trans (mobiusEvalEquiv M1) := by
  ext z
  exact mobiusEvalEquiv_comp_apply M1 M2 z

lemma mobiusEvalEquiv_comp_symm_apply
    (M1 M2 : InfoGeometry.MobiusTransform) (z : InfoGeometry.RiemannSphere) :
    (mobiusEvalEquiv (InfoGeometry.comp M1 M2)).symm z =
      ((mobiusEvalEquiv M2).trans (mobiusEvalEquiv M1)).symm z := by
  rw [mobiusEvalEquiv_comp]

lemma mobiusEvalEquiv_comp_apply_eval
    (M1 M2 : InfoGeometry.MobiusTransform) (z : InfoGeometry.RiemannSphere) :
    mobiusEvalEquiv (InfoGeometry.comp M1 M2) z = M1.eval (M2.eval z) := by
  exact InfoGeometry.eval_comp M1 M2 z

end Experimental.Sandbox.Mobius
