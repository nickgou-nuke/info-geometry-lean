import Experimental.Sandbox.Mobius.CP1Basics

namespace Experimental.Sandbox.Mobius

lemma actCP1_z1
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    (M.actCP1 p).z1 = M.a * p.z1 + M.b * p.z2 := by
  rfl

lemma actCP1_z2
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1) :
    (M.actCP1 p).z2 = M.c * p.z1 + M.d * p.z2 := by
  rfl

lemma actCP1_toRiemannSphere_of_z2_eq_zero
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1)
    (h : M.c * p.z1 + M.d * p.z2 = 0) :
    (M.actCP1 p).toRiemannSphere = none := by
  exact cp1_toRiemannSphere_of_z2_eq_zero (M.actCP1 p) (by simpa [actCP1_z2] using h)

lemma actCP1_toRiemannSphere_of_z2_ne_zero
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1)
    (h : M.c * p.z1 + M.d * p.z2 ≠ 0) :
    (M.actCP1 p).toRiemannSphere =
      some ((M.a * p.z1 + M.b * p.z2) / (M.c * p.z1 + M.d * p.z2)) := by
  have h' : (M.actCP1 p).z2 ≠ 0 := by simpa [actCP1_z2] using h
  rw [cp1_toRiemannSphere_of_z2_ne_zero (M.actCP1 p) h']
  simp [actCP1_z1, actCP1_z2]

lemma actCP1_z1_ne_zero_of_z2_eq_zero
    (M : InfoGeometry.MobiusTransform) (p : InfoGeometry.CP1)
    (h : M.c * p.z1 + M.d * p.z2 = 0) :
    M.a * p.z1 + M.b * p.z2 ≠ 0 := by
  have hzero : (M.actCP1 p).z2 = 0 := by simpa [actCP1_z2] using h
  have hz1 := cp1_z1_ne_zero_of_z2_eq_zero (M.actCP1 p) hzero
  simpa [actCP1_z1] using hz1

end Experimental.Sandbox.Mobius
