import Experimental.Sandbox.Mobius.CP1ActionComposition

namespace Experimental.Sandbox.Mobius

lemma inversion_actCP1_z1 (p : InfoGeometry.CP1) :
    (InfoGeometry.inversion_transform.actCP1 p).z1 = p.z2 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inversion_transform]

lemma inversion_actCP1_z2 (p : InfoGeometry.CP1) :
    (InfoGeometry.inversion_transform.actCP1 p).z2 = p.z1 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inversion_transform]

lemma inversion_actCP1_involutive_z1 (p : InfoGeometry.CP1) :
    (InfoGeometry.inversion_transform.actCP1
        (InfoGeometry.inversion_transform.actCP1 p)).z1 = p.z1 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inversion_transform]

lemma inversion_actCP1_involutive_z2 (p : InfoGeometry.CP1) :
    (InfoGeometry.inversion_transform.actCP1
        (InfoGeometry.inversion_transform.actCP1 p)).z2 = p.z2 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.inversion_transform]

lemma inversion_actCP1_involutive (p : InfoGeometry.CP1) :
    InfoGeometry.inversion_transform.actCP1
        (InfoGeometry.inversion_transform.actCP1 p) = p := by
  apply cp1_ext
  · exact inversion_actCP1_involutive_z1 p
  · exact inversion_actCP1_involutive_z2 p

lemma inversion_actCP1_involutive_toRiemannSphere (p : InfoGeometry.CP1) :
    (InfoGeometry.inversion_transform.actCP1
        (InfoGeometry.inversion_transform.actCP1 p)).toRiemannSphere = p.toRiemannSphere := by
  rw [inversion_actCP1_involutive]

end Experimental.Sandbox.Mobius
