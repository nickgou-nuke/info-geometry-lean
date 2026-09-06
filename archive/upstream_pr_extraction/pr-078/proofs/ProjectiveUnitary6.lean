import Mathlib

/-!
# Algebraic projective unitary six-state layer

This owner records the central-sign quotient used by a projective Klein
relation.  It is deliberately algebraic: it does not construct a topology,
a Klein-bottle fundamental group, a local system, or a Hamiltonian.
-/

namespace ProjectiveUnitary6

abbrev U6 := Matrix.unitaryGroup (Fin 6) ℂ
abbrev CenterU6 := Subgroup.center U6
abbrev PU6 := U6 ⧸ CenterU6

abbrev toPU6 : U6 →* PU6 := QuotientGroup.mk' CenterU6

theorem center_vanishes (z : U6) (hz : z ∈ CenterU6) :
    toPU6 z = 1 := by
  change (QuotientGroup.mk' CenterU6) z = 1
  exact (QuotientGroup.eq_one_iff z).2 hz

theorem projective_conjugation_relation
    (Theta T z : U6) (hz : z ∈ CenterU6)
    (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) :
    toPU6 Theta * toPU6 T * (toPU6 Theta)⁻¹ =
      (toPU6 T)⁻¹ := by
  calc
    toPU6 Theta * toPU6 T * (toPU6 Theta)⁻¹ =
        toPU6 (Theta * T * Theta⁻¹) := by simp
    _ = toPU6 (z * T⁻¹) := by rw [hpin]
    _ = toPU6 z * (toPU6 T)⁻¹ := by simp
    _ = (toPU6 T)⁻¹ := by rw [center_vanishes z hz]; simp

/-- The exact algebraic output of a central-sign Pin relation. -/
theorem projective_unitary6_packet
    (Theta T z : U6) (hz : z ∈ CenterU6)
    (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) :
    toPU6 Theta * toPU6 T * (toPU6 Theta)⁻¹ =
      (toPU6 T)⁻¹ ∧
    toPU6 z = 1 :=
  ⟨projective_conjugation_relation Theta T z hz hpin,
    center_vanishes z hz⟩

end ProjectiveUnitary6
