import Experimental.Sandbox.Mobius.CP1EquivProjection

namespace Experimental.Sandbox.Mobius

lemma actCP1_preserves_equiv
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) :
    InfoGeometry.CP1.equiv (M.actCP1 p) (M.actCP1 q) := by
  rcases h with ⟨lam, hlam, hpq1, hpq2⟩
  refine ⟨lam, hlam, ?_, ?_⟩
  · rw [actCP1_z1, actCP1_z1, hpq1, hpq2]
    ring
  · rw [actCP1_z2, actCP1_z2, hpq1, hpq2]
    ring

lemma actCP1_toRiemannSphere_eq_of_equiv
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) :
    (M.actCP1 p).toRiemannSphere = (M.actCP1 q).toRiemannSphere := by
  exact cp1_equiv_toRiemannSphere (actCP1_preserves_equiv M h)

lemma mobius_eval_toRiemannSphere_eq_of_cp1_equiv
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) :
    M.eval p.toRiemannSphere = M.eval q.toRiemannSphere := by
  rw [← InfoGeometry.mobius_action_correspondence M p,
      ← InfoGeometry.mobius_action_correspondence M q]
  exact actCP1_toRiemannSphere_eq_of_equiv M h

end Experimental.Sandbox.Mobius
