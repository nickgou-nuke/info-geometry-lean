import Experimental.Sandbox.Mobius.CP1EquivProjection

namespace Experimental.Sandbox.Mobius

lemma cp1_equiv_of_toRiemannSphere_eq {p q : InfoGeometry.CP1}
    (h : p.toRiemannSphere = q.toRiemannSphere) :
    InfoGeometry.CP1.equiv p q := by
  by_cases hp2 : p.z2 = 0
  · by_cases hq2 : q.z2 = 0
    · have hp1 : p.z1 ≠ 0 := cp1_z1_ne_zero_of_z2_eq_zero p hp2
      have hq1 : q.z1 ≠ 0 := cp1_z1_ne_zero_of_z2_eq_zero q hq2
      refine ⟨p.z1 / q.z1, div_ne_zero hp1 hq1, ?_, ?_⟩
      · rw [div_mul_cancel₀ p.z1 hq1]
      · rw [hp2, hq2]
        simp
    · rw [cp1_toRiemannSphere_of_z2_eq_zero p hp2,
          cp1_toRiemannSphere_of_z2_ne_zero q hq2] at h
      cases h
  · by_cases hq2 : q.z2 = 0
    · rw [cp1_toRiemannSphere_of_z2_ne_zero p hp2,
          cp1_toRiemannSphere_of_z2_eq_zero q hq2] at h
      cases h
    · have hratio : p.z1 / p.z2 = q.z1 / q.z2 := by
        rw [cp1_toRiemannSphere_of_z2_ne_zero p hp2,
            cp1_toRiemannSphere_of_z2_ne_zero q hq2] at h
        exact Option.some.inj h
      refine ⟨p.z2 / q.z2, div_ne_zero hp2 hq2, ?_, ?_⟩
      · calc
          p.z1 = (p.z1 / p.z2) * p.z2 := by
            rw [div_mul_cancel₀ p.z1 hp2]
          _ = (q.z1 / q.z2) * p.z2 := by rw [hratio]
          _ = (p.z2 / q.z2) * q.z1 := by
            field_simp [hq2]
      · rw [div_mul_cancel₀ p.z2 hq2]

lemma cp1_toRiemannSphere_eq_iff {p q : InfoGeometry.CP1} :
    p.toRiemannSphere = q.toRiemannSphere ↔ InfoGeometry.CP1.equiv p q := by
  constructor
  · exact cp1_equiv_of_toRiemannSphere_eq
  · exact cp1_equiv_toRiemannSphere

lemma cp1_equiv_iff_toRiemannSphere_eq {p q : InfoGeometry.CP1} :
    InfoGeometry.CP1.equiv p q ↔ p.toRiemannSphere = q.toRiemannSphere := by
  constructor
  · exact cp1_equiv_toRiemannSphere
  · exact cp1_equiv_of_toRiemannSphere_eq

end Experimental.Sandbox.Mobius
