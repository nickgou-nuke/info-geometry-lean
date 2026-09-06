import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyDualityParitySubmoduleBridge
import InfoGeometry.Canonical.CayleyUnitActionBridge

/-!
# Native Cayley/Hodge unit action on parity sectors

The three named Cayley/Hodge units act on the four parity sectors by the
permutations already proved for their underlying endomorphisms.  This is a
unit-action API only; it does not identify the sectors with physical fields or
assert a completed representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyDualityUnitSectorBridge

open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
open InfoGeometry.Canonical.CayleyPeirceKleinFourBridge
open InfoGeometry.Canonical.CayleyDualityParityActionBridge
open InfoGeometry.Canonical.CayleyDualityParitySubmoduleBridge
open InfoGeometry.Canonical.CayleyDualityUnitsBridge
open InfoGeometry.Canonical.CayleyUnitActionBridge

abbrev Coord := CayleyPeirceKleinFourBridge.Coord
abbrev CoordEnd := CayleyPeirceKleinFourBridge.CoordEnd

theorem C_unit_smul_mem_E_plus_plus
    {x : Coord} (hx : x ∈ E_plus_plus) :
    C_unit • x ∈ E_minus_minus := by
  simpa [unit_smul_eq_val, C_unit_val] using
    (cayleyConj_maps_E_plus_plus_to_E_minus_minus hx)

theorem C_unit_smul_mem_E_minus_minus
    {x : Coord} (hx : x ∈ E_minus_minus) :
    C_unit • x ∈ E_plus_plus := by
  simpa [unit_smul_eq_val, C_unit_val] using
    (cayleyConj_maps_E_minus_minus_to_E_plus_plus hx)

theorem C_unit_smul_mem_E_plus_minus
    {x : Coord} (hx : x ∈ E_plus_minus) :
    C_unit • x ∈ E_plus_minus := by
  simpa [unit_smul_eq_val, C_unit_val] using
    (cayleyConj_preserves_E_plus_minus hx)

theorem C_unit_smul_mem_E_minus_plus
    {x : Coord} (hx : x ∈ E_minus_plus) :
    C_unit • x ∈ E_minus_plus := by
  simpa [unit_smul_eq_val, C_unit_val] using
    (cayleyConj_preserves_E_minus_plus hx)

theorem Star_unit_smul_mem_E_plus_plus
    {x : Coord} (hx : x ∈ E_plus_plus) :
    Star_unit • x ∈ E_minus_minus := by
  simpa [unit_smul_eq_val, Star_unit_val] using
    (hodgeStar_maps_E_plus_plus_to_E_minus_minus hx)

theorem Star_unit_smul_mem_E_minus_minus
    {x : Coord} (hx : x ∈ E_minus_minus) :
    Star_unit • x ∈ E_plus_plus := by
  simpa [unit_smul_eq_val, Star_unit_val] using
    (hodgeStar_maps_E_minus_minus_to_E_plus_plus hx)

theorem Star_unit_smul_mem_E_plus_minus
    {x : Coord} (hx : x ∈ E_plus_minus) :
    Star_unit • x ∈ E_minus_plus := by
  simpa [unit_smul_eq_val, Star_unit_val] using
    (hodgeStar_maps_E_plus_minus_to_E_minus_plus hx)

theorem Star_unit_smul_mem_E_minus_plus
    {x : Coord} (hx : x ∈ E_minus_plus) :
    Star_unit • x ∈ E_plus_minus := by
  simpa [unit_smul_eq_val, Star_unit_val] using
    (hodgeStar_maps_E_minus_plus_to_E_plus_minus hx)

theorem Xi_unit_smul_mem_E_plus_plus
    {x : Coord} (hx : x ∈ E_plus_plus) :
    Xi_unit • x ∈ E_plus_plus := by
  simpa [unit_smul_eq_val, Xi_unit_val] using
    (middleExchangeFlip_preserves_E_plus_plus hx)

theorem Xi_unit_smul_mem_E_minus_minus
    {x : Coord} (hx : x ∈ E_minus_minus) :
    Xi_unit • x ∈ E_minus_minus := by
  simpa [unit_smul_eq_val, Xi_unit_val] using
    (middleExchangeFlip_preserves_E_minus_minus hx)

theorem Xi_unit_smul_mem_E_plus_minus
    {x : Coord} (hx : x ∈ E_plus_minus) :
    Xi_unit • x ∈ E_minus_plus := by
  simpa [unit_smul_eq_val, Xi_unit_val] using
    (middleExchangeFlip_maps_E_plus_minus_to_E_minus_plus hx)

theorem Xi_unit_smul_mem_E_minus_plus
    {x : Coord} (hx : x ∈ E_minus_plus) :
    Xi_unit • x ∈ E_plus_minus := by
  simpa [unit_smul_eq_val, Xi_unit_val] using
    (middleExchangeFlip_maps_E_minus_plus_to_E_plus_minus hx)

theorem C_unit_map_E_plus_plus :
    Submodule.map (C_unit : CoordEnd) E_plus_plus = E_minus_minus := by
  simpa [C_unit_val] using cayleyConj_map_E_plus_plus

theorem C_unit_map_E_minus_minus :
    Submodule.map (C_unit : CoordEnd) E_minus_minus = E_plus_plus := by
  simpa [C_unit_val] using cayleyConj_map_E_minus_minus

theorem C_unit_map_E_plus_minus :
    Submodule.map (C_unit : CoordEnd) E_plus_minus = E_plus_minus := by
  simpa [C_unit_val] using cayleyConj_map_E_plus_minus

theorem C_unit_map_E_minus_plus :
    Submodule.map (C_unit : CoordEnd) E_minus_plus = E_minus_plus := by
  simpa [C_unit_val] using cayleyConj_map_E_minus_plus

theorem Star_unit_map_E_plus_plus :
    Submodule.map (Star_unit : CoordEnd) E_plus_plus = E_minus_minus := by
  simpa [Star_unit_val] using hodgeStar_map_E_plus_plus

theorem Star_unit_map_E_minus_minus :
    Submodule.map (Star_unit : CoordEnd) E_minus_minus = E_plus_plus := by
  simpa [Star_unit_val] using hodgeStar_map_E_minus_minus

theorem Star_unit_map_E_plus_minus :
    Submodule.map (Star_unit : CoordEnd) E_plus_minus = E_minus_plus := by
  simpa [Star_unit_val] using hodgeStar_map_E_plus_minus

theorem Star_unit_map_E_minus_plus :
    Submodule.map (Star_unit : CoordEnd) E_minus_plus = E_plus_minus := by
  simpa [Star_unit_val] using hodgeStar_map_E_minus_plus

theorem Xi_unit_map_E_plus_plus :
    Submodule.map (Xi_unit : CoordEnd) E_plus_plus = E_plus_plus := by
  simpa [Xi_unit_val] using middleExchangeFlip_map_E_plus_plus

theorem Xi_unit_map_E_minus_minus :
    Submodule.map (Xi_unit : CoordEnd) E_minus_minus = E_minus_minus := by
  simpa [Xi_unit_val] using middleExchangeFlip_map_E_minus_minus

theorem Xi_unit_map_E_plus_minus :
    Submodule.map (Xi_unit : CoordEnd) E_plus_minus = E_minus_plus := by
  simpa [Xi_unit_val] using middleExchangeFlip_map_E_plus_minus

theorem Xi_unit_map_E_minus_plus :
    Submodule.map (Xi_unit : CoordEnd) E_minus_plus = E_plus_minus := by
  simpa [Xi_unit_val] using middleExchangeFlip_map_E_minus_plus

end InfoGeometry.Canonical.CayleyDualityUnitSectorBridge
