import InfoGeometry.Topology.MobiusGeometry

namespace Experimental.Sandbox.Mobius

lemma cp1_toRiemannSphere_of_z2_eq_zero
    (p : InfoGeometry.CP1) (h : p.z2 = 0) :
    p.toRiemannSphere = none := by
  simp [InfoGeometry.CP1.toRiemannSphere, h]

lemma cp1_toRiemannSphere_of_z2_ne_zero
    (p : InfoGeometry.CP1) (h : p.z2 ≠ 0) :
    p.toRiemannSphere = some (p.z1 / p.z2) := by
  simp [InfoGeometry.CP1.toRiemannSphere, h]

lemma cp1_z1_ne_zero_of_z2_eq_zero
    (p : InfoGeometry.CP1) (h : p.z2 = 0) :
    p.z1 ≠ 0 := by
  rcases p.not_both_zero with h1 | h2
  · exact h1
  · exact False.elim (h2 h)

lemma cp1_equiv_refl (p : InfoGeometry.CP1) :
    InfoGeometry.CP1.equiv p p := by
  refine ⟨1, one_ne_zero, ?_, ?_⟩ <;> simp

lemma cp1_equiv_symm {p q : InfoGeometry.CP1} :
    InfoGeometry.CP1.equiv p q → InfoGeometry.CP1.equiv q p := by
  rintro ⟨lam, hlam, hz1, hz2⟩
  refine ⟨lam⁻¹, inv_ne_zero hlam, ?_, ?_⟩
  · rw [hz1]
    field_simp [hlam]
  · rw [hz2]
    field_simp [hlam]

lemma cp1_equiv_trans {p q r : InfoGeometry.CP1} :
    InfoGeometry.CP1.equiv p q → InfoGeometry.CP1.equiv q r → InfoGeometry.CP1.equiv p r := by
  rintro ⟨lam, hlam, hpq1, hpq2⟩ ⟨mu, hmu, hqr1, hqr2⟩
  refine ⟨lam * mu, mul_ne_zero hlam hmu, ?_, ?_⟩
  · rw [hpq1, hqr1]
    ring
  · rw [hpq2, hqr2]
    ring

end Experimental.Sandbox.Mobius
