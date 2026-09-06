import Experimental.Sandbox.Mobius.CP1ActionComposition

namespace Experimental.Sandbox.Mobius

lemma translation_zero_actCP1_z1 (p : InfoGeometry.CP1) :
    ((InfoGeometry.translation_transform 0).actCP1 p).z1 = p.z1 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.translation_transform]

lemma translation_zero_actCP1_z2 (p : InfoGeometry.CP1) :
    ((InfoGeometry.translation_transform 0).actCP1 p).z2 = p.z2 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.translation_transform]

lemma translation_zero_actCP1 (p : InfoGeometry.CP1) :
    (InfoGeometry.translation_transform 0).actCP1 p = p := by
  apply cp1_ext
  · exact translation_zero_actCP1_z1 p
  · exact translation_zero_actCP1_z2 p

lemma dilation_one_actCP1_z1 (p : InfoGeometry.CP1) :
    ((InfoGeometry.dilation_transform 1 one_ne_zero).actCP1 p).z1 = p.z1 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.dilation_transform]

lemma dilation_one_actCP1_z2 (p : InfoGeometry.CP1) :
    ((InfoGeometry.dilation_transform 1 one_ne_zero).actCP1 p).z2 = p.z2 := by
  simp [InfoGeometry.MobiusTransform.actCP1, InfoGeometry.dilation_transform]

lemma dilation_one_actCP1 (p : InfoGeometry.CP1) :
    (InfoGeometry.dilation_transform 1 one_ne_zero).actCP1 p = p := by
  apply cp1_ext
  · exact dilation_one_actCP1_z1 p
  · exact dilation_one_actCP1_z2 p

end Experimental.Sandbox.Mobius
