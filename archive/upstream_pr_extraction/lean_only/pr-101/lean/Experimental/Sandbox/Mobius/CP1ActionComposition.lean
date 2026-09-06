import Experimental.Sandbox.Mobius.CP1ActionEquiv
import Experimental.Sandbox.Mobius.CompositionFinite

namespace Experimental.Sandbox.Mobius

lemma cp1_ext
    {p q : InfoGeometry.CP1}
    (hz1 : p.z1 = q.z1) (hz2 : p.z2 = q.z2) : p = q := by
  cases p
  cases q
  simp at hz1 hz2
  subst_vars
  rfl

lemma actCP1_comp_z1
    (M1 M2 : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    ((InfoGeometry.comp M1 M2).actCP1 p).z1 =
      (M1.actCP1 (M2.actCP1 p)).z1 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.comp]
  ring

lemma actCP1_comp_z2
    (M1 M2 : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    ((InfoGeometry.comp M1 M2).actCP1 p).z2 =
      (M1.actCP1 (M2.actCP1 p)).z2 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.comp]
  ring

lemma actCP1_comp
    (M1 M2 : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    (InfoGeometry.comp M1 M2).actCP1 p = M1.actCP1 (M2.actCP1 p) := by
  apply cp1_ext
  · exact actCP1_comp_z1 M1 M2 p
  · exact actCP1_comp_z2 M1 M2 p

lemma actCP1_comp_toRiemannSphere
    (M1 M2 : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    ((InfoGeometry.comp M1 M2).actCP1 p).toRiemannSphere =
      (M1.actCP1 (M2.actCP1 p)).toRiemannSphere := by
  rw [actCP1_comp]

end Experimental.Sandbox.Mobius
