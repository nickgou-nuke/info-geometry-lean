import InfoGeometry.Clifford.Cl55WittReflectionPairDeterminant
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

noncomputable section

/-!
# Determinant parity for finite anisotropic reflection words

This owner proves the finite parity statement needed by a
Cartan--Dieudonne-style orientation argument.  It does not assert that every
native `Spin55` element has a word presentation of this form.
-/

abbrev AnisotropicVector55 := {v : V55 // Q55 v ≠ 0}

noncomputable def specialOrthogonalGroup55 : Subgroup orthogonalGroup55 where
  carrier := {g | g.1.det = (1 : ℝˣ)}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g.1 * h.1).det = (1 : ℝˣ)
    rw [map_mul, hg, hh]
    simp
  inv_mem' := by
    intro g hg
    change (g.1⁻¹).det = (1 : ℝˣ)
    have hdet : (g.1⁻¹).det = (g.1.det)⁻¹ := by
      exact (LinearEquiv.det (R := ℝ) (M := V55)).map_inv g.1
    rw [hdet, hg]
    simp

noncomputable def quadraticReflectionWord :
    List AnisotropicVector55 → orthogonalGroup55
  | [] => 1
  | v :: vs =>
      quadraticReflectionElement v.1 v.2 * quadraticReflectionWord vs

theorem quadraticReflectionWord_det
    (vs : List AnisotropicVector55) :
    (quadraticReflectionWord vs).1.det =
      (-1 : ℝˣ) ^ vs.length := by
  induction vs with
  | nil =>
      simp [quadraticReflectionWord]
  | cons v vs ih =>
      change LinearEquiv.det
        ((quadraticReflectionElement v.1 v.2).1 *
          (quadraticReflectionWord vs).1) = _
      rw [map_mul, quadraticReflectionElement_det v.1 v.2, ih]
      simp [pow_succ, mul_comm]

theorem quadraticReflectionWord_det_eq_one_of_even
    (vs : List AnisotropicVector55)
    (heven : Even vs.length) :
      (quadraticReflectionWord vs).1.det = (1 : ℝˣ) := by
  rw [quadraticReflectionWord_det]
  rcases heven with ⟨k, hk⟩
  rw [hk, pow_add]
  rw [← pow_add]
  simp

theorem quadraticReflectionWord_mem_specialOrthogonalGroup55_of_even
    (vs : List AnisotropicVector55)
    (heven : Even vs.length) :
    quadraticReflectionWord vs ∈ specialOrthogonalGroup55 := by
  exact quadraticReflectionWord_det_eq_one_of_even vs heven

theorem quadraticReflectionWord_det_eq_one_iff_even
    (vs : List AnisotropicVector55) :
    (quadraticReflectionWord vs).1.det = (1 : ℝˣ) ↔
      Even vs.length := by
  rw [quadraticReflectionWord_det]
  exact neg_one_pow_eq_one_iff_even (by norm_num)

end

end InfoGeometry.Clifford.Clifford55
