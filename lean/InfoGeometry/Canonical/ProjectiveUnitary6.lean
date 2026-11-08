import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ProjectiveUnitary6

abbrev U6 := ↥(Matrix.unitaryGroup (Fin 6) ℂ)

abbrev centerU6 : Subgroup U6 := Subgroup.center U6

abbrev PU6 := U6 ⧸ centerU6

def toPU6 : U6 →* PU6 := QuotientGroup.mk' centerU6

theorem toPU6_z_eq_one (z : U6) (hz : z ∈ centerU6) : toPU6 z = 1 := by
  exact (QuotientGroup.eq_one_iff z).mpr hz

theorem toPU6_eq_iff (u v : U6) :
    toPU6 u = toPU6 v ↔ u * v⁻¹ ∈ centerU6 := by
  rw [show toPU6 u = toPU6 v ↔ toPU6 (u * v⁻¹) = 1 by
    constructor
    · intro h
      rw [map_mul, map_inv, h]
      simp
    · intro h
      have hz : toPU6 (u * v⁻¹) = 1 := h
      apply (mul_right_cancel (b := (toPU6 v)⁻¹))
      simpa [map_mul, map_inv] using hz]
  exact QuotientGroup.eq_one_iff _

theorem projective_conjugation_relation (Theta T z : U6) (hz : z ∈ centerU6) (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) :
    toPU6 Theta * toPU6 T * (toPU6 Theta)⁻¹ = (toPU6 T)⁻¹ := by
  calc
    toPU6 Theta * toPU6 T * (toPU6 Theta)⁻¹
        = toPU6 (Theta * T * Theta⁻¹) := by simp [map_mul, map_inv, mul_assoc]
    _ = toPU6 (z * T⁻¹) := by rw [hpin]
    _ = (toPU6 T)⁻¹ := by simp [map_mul, map_inv, toPU6_z_eq_one _ hz]

end InfoGeometry.Canonical.ProjectiveUnitary6
