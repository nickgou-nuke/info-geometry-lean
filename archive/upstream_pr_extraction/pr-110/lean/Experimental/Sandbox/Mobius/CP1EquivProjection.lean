import Experimental.Sandbox.Mobius.CP1ChartPoints

namespace Experimental.Sandbox.Mobius

lemma cp1_equiv_z2_eq_zero_iff {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) :
    p.z2 = 0 ↔ q.z2 = 0 := by
  rcases h with ⟨lam, hlam, _hz1, hz2⟩
  constructor
  · intro hp
    rw [hz2] at hp
    exact (mul_eq_zero.mp hp).resolve_left hlam
  · intro hq
    rw [hz2, hq, mul_zero]

lemma cp1_equiv_z2_ne_zero_iff {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) :
    p.z2 ≠ 0 ↔ q.z2 ≠ 0 := by
  rw [ne_eq, ne_eq, not_iff_not]
  exact cp1_equiv_z2_eq_zero_iff h

lemma cp1_equiv_affine_ratio_eq {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) (hq2 : q.z2 ≠ 0) :
    p.z1 / p.z2 = q.z1 / q.z2 := by
  rcases h with ⟨lam, hlam, hz1, hz2⟩
  have hp2 : p.z2 ≠ 0 := (cp1_equiv_z2_ne_zero_iff ⟨lam, hlam, hz1, hz2⟩).mpr hq2
  rw [hz1, hz2]
  exact mul_div_mul_left q.z1 q.z2 hlam

lemma cp1_equiv_toRiemannSphere {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv p q) :
    p.toRiemannSphere = q.toRiemannSphere := by
  by_cases hq2 : q.z2 = 0
  · have hp2 : p.z2 = 0 := (cp1_equiv_z2_eq_zero_iff h).mpr hq2
    rw [cp1_toRiemannSphere_of_z2_eq_zero p hp2,
        cp1_toRiemannSphere_of_z2_eq_zero q hq2]
  · have hp2 : p.z2 ≠ 0 := (cp1_equiv_z2_ne_zero_iff h).mpr hq2
    rw [cp1_toRiemannSphere_of_z2_ne_zero p hp2,
        cp1_toRiemannSphere_of_z2_ne_zero q hq2]
    congr 1
    exact cp1_equiv_affine_ratio_eq h hq2

end Experimental.Sandbox.Mobius
