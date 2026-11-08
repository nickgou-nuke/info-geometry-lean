import Experimental.Sandbox.Mobius.EvalInjective

namespace Experimental.Sandbox.Mobius

lemma mobius_eval_surjective (M : InfoGeometry.MobiusTransform) :
    Function.Surjective M.eval := by
  intro z
  refine ⟨(InfoGeometry.inv M).eval z, ?_⟩
  exact InfoGeometry.eval_inv M z

lemma mobius_eval_bijective (M : InfoGeometry.MobiusTransform) :
    Function.Bijective M.eval := by
  exact ⟨mobius_eval_injective M, mobius_eval_surjective M⟩

lemma mobius_eval_inv_rightInverse (M : InfoGeometry.MobiusTransform) :
    Function.RightInverse (InfoGeometry.inv M).eval M.eval := by
  intro z
  exact InfoGeometry.eval_inv M z

lemma mobius_eval_inv_leftInverse (M : InfoGeometry.MobiusTransform) :
    Function.LeftInverse (InfoGeometry.inv M).eval M.eval := by
  intro z
  exact InfoGeometry.eval_inv_left M z

lemma mobius_eval_preimage_witness (M : InfoGeometry.MobiusTransform)
    (z : InfoGeometry.RiemannSphere) :
    M.eval ((InfoGeometry.inv M).eval z) = z := by
  exact InfoGeometry.eval_inv M z

end Experimental.Sandbox.Mobius
