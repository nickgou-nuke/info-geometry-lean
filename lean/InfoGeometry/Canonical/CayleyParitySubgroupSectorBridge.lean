import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyUnitActionBridge

/-!
# Parity Klein subgroup action on the joint sectors

This owner records the algebraic sector invariance of the native parity Klein
subgroup action.  It uses the already constructed unit action and the explicit
four-element packet; it does not add a new representation or a physical
interpretation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyParitySubgroupSectorBridge

open InfoGeometry.Canonical.CayleyPeirceKleinFourBridge
open InfoGeometry.Canonical.CayleyWittenPeirceParityBridge
open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
open InfoGeometry.Canonical.CayleyParityUnitsBridge
open InfoGeometry.Canonical.CayleyUnitActionBridge

abbrev Coord := CayleyPeirceKleinFourBridge.Coord
abbrev CoordEnd := CayleyPeirceKleinFourBridge.CoordEnd

private theorem parity_packet_cases
    (u : parityKleinSubgroup) :
    (u : CoordEndˣ) = 1 ∨
      (u : CoordEndˣ) = P_unit ∨
      (u : CoordEndˣ) = GammaF_unit ∨
      (u : CoordEndˣ) = M_mid_unit := by
  have hu := parityKleinSubgroup_mem_parityUnitPacket u
  simpa only [parityUnitPacket, Set.mem_insert_iff, Set.mem_singleton_iff] using hu

theorem parity_subgroup_smul_mem_E_plus_plus
    (u : parityKleinSubgroup) {x : Coord} (hx : x ∈ E_plus_plus) :
    u • x ∈ E_plus_plus := by
  rw [mem_E_plus_plus_iff] at hx ⊢
  rcases parity_packet_cases u with h | h | h | h
  · simpa [parity_subgroup_smul_eq_ambient, h] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, P_unit_val, P,
      peirceGrading] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, GammaF_unit_val, GammaF,
      exteriorFermionParity] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, M_mid_unit_val, M_mid,
      middleSignFlip] using hx

theorem parity_subgroup_smul_mem_E_plus_minus
    (u : parityKleinSubgroup) {x : Coord} (hx : x ∈ E_plus_minus) :
    u • x ∈ E_plus_minus := by
  rw [mem_E_plus_minus_iff] at hx ⊢
  rcases parity_packet_cases u with h | h | h | h
  · simpa [parity_subgroup_smul_eq_ambient, h] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, P_unit_val, P,
      peirceGrading] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, GammaF_unit_val, GammaF,
      exteriorFermionParity] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, M_mid_unit_val, M_mid,
      middleSignFlip] using hx

theorem parity_subgroup_smul_mem_E_minus_plus
    (u : parityKleinSubgroup) {x : Coord} (hx : x ∈ E_minus_plus) :
    u • x ∈ E_minus_plus := by
  rw [mem_E_minus_plus_iff] at hx ⊢
  rcases parity_packet_cases u with h | h | h | h
  · simpa [parity_subgroup_smul_eq_ambient, h] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, P_unit_val, P,
      peirceGrading] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, GammaF_unit_val, GammaF,
      exteriorFermionParity] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, M_mid_unit_val, M_mid,
      middleSignFlip] using hx

theorem parity_subgroup_smul_mem_E_minus_minus
    (u : parityKleinSubgroup) {x : Coord} (hx : x ∈ E_minus_minus) :
    u • x ∈ E_minus_minus := by
  rw [mem_E_minus_minus_iff] at hx ⊢
  rcases parity_packet_cases u with h | h | h | h
  · simpa [parity_subgroup_smul_eq_ambient, h] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, P_unit_val, P,
      peirceGrading] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, GammaF_unit_val, GammaF,
      exteriorFermionParity] using hx
  · simpa [parity_subgroup_smul_eq_ambient, h, M_mid_unit_val, M_mid,
      middleSignFlip] using hx

end InfoGeometry.Canonical.CayleyParitySubgroupSectorBridge
