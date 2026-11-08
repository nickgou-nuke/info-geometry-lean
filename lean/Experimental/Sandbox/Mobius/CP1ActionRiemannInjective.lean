import Experimental.Sandbox.Mobius.CP1ActionEquivIff
import Experimental.Sandbox.Mobius.CP1RiemannSphereEquiv

namespace Experimental.Sandbox.Mobius

lemma actCP1_toRiemannSphere_eq_iff
    (M : InfoGeometry.MobiusTransform) (p q : InfoGeometry.CP1) :
    (M.actCP1 p).toRiemannSphere = (M.actCP1 q).toRiemannSphere ↔
      p.toRiemannSphere = q.toRiemannSphere := by
  rw [cp1_toRiemannSphere_eq_iff, cp1_toRiemannSphere_eq_iff,
    actCP1_equiv_iff]

lemma mobius_eval_toRiemannSphere_eq_iff
    (M : InfoGeometry.MobiusTransform) (p q : InfoGeometry.CP1) :
    M.eval p.toRiemannSphere = M.eval q.toRiemannSphere ↔
      p.toRiemannSphere = q.toRiemannSphere := by
  rw [← InfoGeometry.mobius_action_correspondence M p,
      ← InfoGeometry.mobius_action_correspondence M q,
      actCP1_toRiemannSphere_eq_iff M p q]

lemma mobius_eval_toRiemannSphere_eq_of_eq
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : p.toRiemannSphere = q.toRiemannSphere) :
    M.eval p.toRiemannSphere = M.eval q.toRiemannSphere := by
  exact (mobius_eval_toRiemannSphere_eq_iff M p q).mpr h

lemma toRiemannSphere_eq_of_mobius_eval_toRiemannSphere_eq
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : M.eval p.toRiemannSphere = M.eval q.toRiemannSphere) :
    p.toRiemannSphere = q.toRiemannSphere := by
  exact (mobius_eval_toRiemannSphere_eq_iff M p q).mp h

end Experimental.Sandbox.Mobius
