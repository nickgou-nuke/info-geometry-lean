import Experimental.Sandbox.Mobius.CP1ActionCoordinates

namespace Experimental.Sandbox.Mobius

def cp1Infinity : InfoGeometry.CP1 :=
  { z1 := 1
    z2 := 0
    not_both_zero := Or.inl one_ne_zero }

def cp1Affine (z : ℂ) : InfoGeometry.CP1 :=
  { z1 := z
    z2 := 1
    not_both_zero := Or.inr one_ne_zero }

lemma cp1Infinity_toRiemannSphere :
    cp1Infinity.toRiemannSphere = none := by
  simp [cp1Infinity, InfoGeometry.CP1.toRiemannSphere]

lemma cp1Affine_toRiemannSphere (z : ℂ) :
    (cp1Affine z).toRiemannSphere = some z := by
  simp [cp1Affine, InfoGeometry.CP1.toRiemannSphere]

lemma cp1Affine_equiv_iff (z w : ℂ) :
    InfoGeometry.CP1.equiv (cp1Affine z) (cp1Affine w) ↔ z = w := by
  constructor
  · rintro ⟨lam, _hlam, hz, hone⟩
    have hlam : lam = 1 := by
      simpa [cp1Affine] using hone.symm
    simpa [cp1Affine, hlam] using hz
  · intro h
    subst w
    exact cp1_equiv_refl (cp1Affine z)

lemma cp1Infinity_not_equiv_cp1Affine (z : ℂ) :
    ¬ InfoGeometry.CP1.equiv cp1Infinity (cp1Affine z) := by
  rintro ⟨lam, hlam, _hz1, hz2⟩
  have hlam0 : lam = 0 := by
    simpa [cp1Infinity, cp1Affine] using hz2.symm
  exact hlam hlam0

lemma cp1Affine_not_equiv_cp1Infinity (z : ℂ) :
    ¬ InfoGeometry.CP1.equiv (cp1Affine z) cp1Infinity := by
  intro h
  exact cp1Infinity_not_equiv_cp1Affine z (cp1_equiv_symm h)

lemma actCP1_cp1Affine_toRiemannSphere_of_den_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hden : M.c * z + M.d ≠ 0) :
    (M.actCP1 (cp1Affine z)).toRiemannSphere =
      some ((M.a * z + M.b) / (M.c * z + M.d)) := by
  have h : M.c * (cp1Affine z).z1 + M.d * (cp1Affine z).z2 ≠ 0 := by
    simpa [cp1Affine] using hden
  simpa [cp1Affine] using actCP1_toRiemannSphere_of_z2_ne_zero M (cp1Affine z) h

lemma actCP1_cp1Affine_toRiemannSphere_of_den_eq_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hden : M.c * z + M.d = 0) :
    (M.actCP1 (cp1Affine z)).toRiemannSphere = none := by
  have h : M.c * (cp1Affine z).z1 + M.d * (cp1Affine z).z2 = 0 := by
    simpa [cp1Affine] using hden
  simpa [cp1Affine] using actCP1_toRiemannSphere_of_z2_eq_zero M (cp1Affine z) h

lemma actCP1_cp1Infinity_toRiemannSphere_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (hc : M.c = 0) :
    (M.actCP1 cp1Infinity).toRiemannSphere = none := by
  have h : M.c * cp1Infinity.z1 + M.d * cp1Infinity.z2 = 0 := by
    simp [cp1Infinity, hc]
  exact actCP1_toRiemannSphere_of_z2_eq_zero M cp1Infinity h

lemma actCP1_cp1Infinity_toRiemannSphere_of_c_ne_zero
    (M : InfoGeometry.MobiusTransform) (hc : M.c ≠ 0) :
    (M.actCP1 cp1Infinity).toRiemannSphere = some (M.a / M.c) := by
  have h : M.c * cp1Infinity.z1 + M.d * cp1Infinity.z2 ≠ 0 := by
    simpa [cp1Infinity] using hc
  simpa [cp1Infinity] using actCP1_toRiemannSphere_of_z2_ne_zero M cp1Infinity h

end Experimental.Sandbox.Mobius
