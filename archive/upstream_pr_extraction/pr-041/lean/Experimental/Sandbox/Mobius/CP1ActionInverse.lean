import Experimental.Sandbox.Mobius.CP1ActionComposition

namespace Experimental.Sandbox.Mobius

lemma inv_actCP1_after_actCP1_equiv
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    InfoGeometry.CP1.equiv ((InfoGeometry.inv M).actCP1 (M.actCP1 p)) p := by
  refine ⟨M.a * M.d - M.b * M.c, M.det_ne_zero, ?_, ?_⟩
  · simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inv]
    ring
  · simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inv]
    ring

lemma actCP1_after_inv_actCP1_equiv
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    InfoGeometry.CP1.equiv (M.actCP1 ((InfoGeometry.inv M).actCP1 p)) p := by
  refine ⟨M.a * M.d - M.b * M.c, M.det_ne_zero, ?_, ?_⟩
  · simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inv]
    ring
  · simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inv]
    ring

lemma inv_actCP1_after_actCP1_toRiemannSphere
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    ((InfoGeometry.inv M).actCP1 (M.actCP1 p)).toRiemannSphere = p.toRiemannSphere := by
  exact cp1_equiv_toRiemannSphere (inv_actCP1_after_actCP1_equiv M p)

lemma actCP1_after_inv_actCP1_toRiemannSphere
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    (M.actCP1 ((InfoGeometry.inv M).actCP1 p)).toRiemannSphere = p.toRiemannSphere := by
  exact cp1_equiv_toRiemannSphere (actCP1_after_inv_actCP1_equiv M p)

end Experimental.Sandbox.Mobius
