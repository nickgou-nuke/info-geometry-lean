import InfoGeometry.Canonical.CayleyDualitySectorPermutationBridge
import InfoGeometry.Canonical.CayleyDualityUnitSectorBridge

/-!
# Concrete realization of the Cayley/Hodge sector permutation

This consumer identifies the finite permutation labels with the already
proved native `Submodule.map` transport of the three Cayley/Hodge units.  It
does not identify the labels with physical fields or add a group action on a
larger carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyDualitySectorPermutationConcreteBridge

open InfoGeometry.Canonical.CayleyPeirceKleinFourBridge
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Canonical.CayleyDualitySectorPermutationBridge
open InfoGeometry.Canonical.CayleyDualityUnitsBridge
open InfoGeometry.Canonical.CayleyDualityUnitSectorBridge

abbrev Coord := CayleyPeirceKleinFourBridge.Coord
abbrev CoordEnd := CayleyPeirceKleinFourBridge.CoordEnd

def paritySectorSubmodule : ParitySector → Submodule ℝ Coord
  | .plusPlus => E_plus_plus
  | .plusMinus => E_plus_minus
  | .minusPlus => E_minus_plus
  | .minusMinus => E_minus_minus

def unitForV4 : V4Group → CoordEndˣ
  | .I => 1
  | .W1 => C_unit
  | .W2 => Xi_unit
  | .W12 => Star_unit

def unitForV4Hom : V4Group →* CoordEndˣ where
  toFun := unitForV4
  map_one' := by rfl
  map_mul' := by
    intro g h
    cases g <;> cases h <;>
      change unitForV4 (v4_mul _ _) = _ <;>
      simp only [v4_mul, unitForV4] <;>
      simp [C_unit_mul_Star_unit, Star_unit_mul_C_unit,
        Star_unit_mul_Xi_unit, Xi_unit_mul_Star_unit,
        Xi_unit_mul_C_unit, C_unit_mul_Xi_unit]

theorem C_unit_map_paritySector (s : ParitySector) :
    Submodule.map (C_unit : CoordEnd) (paritySectorSubmodule s) =
      paritySectorSubmodule (sectorC s) := by
  cases s
  · simpa [paritySectorSubmodule, sectorC, C_unit_val, sectorC_plusPlus] using C_unit_map_E_plus_plus
  · simpa [paritySectorSubmodule, sectorC, C_unit_val, sectorC_plusMinus] using C_unit_map_E_plus_minus
  · simpa [paritySectorSubmodule, sectorC, C_unit_val, sectorC_minusPlus] using C_unit_map_E_minus_plus
  · simpa [paritySectorSubmodule, sectorC, C_unit_val, sectorC_minusMinus] using C_unit_map_E_minus_minus

theorem Star_unit_map_paritySector (s : ParitySector) :
    Submodule.map (Star_unit : CoordEnd) (paritySectorSubmodule s) =
      paritySectorSubmodule (sectorStar s) := by
  cases s
  · simpa [paritySectorSubmodule, sectorStar, Star_unit_val, sectorStar_plusPlus] using Star_unit_map_E_plus_plus
  · simpa [paritySectorSubmodule, sectorStar, Star_unit_val, sectorStar_plusMinus] using Star_unit_map_E_plus_minus
  · simpa [paritySectorSubmodule, sectorStar, Star_unit_val, sectorStar_minusPlus] using Star_unit_map_E_minus_plus
  · simpa [paritySectorSubmodule, sectorStar, Star_unit_val, sectorStar_minusMinus] using Star_unit_map_E_minus_minus

theorem Xi_unit_map_paritySector (s : ParitySector) :
    Submodule.map (Xi_unit : CoordEnd) (paritySectorSubmodule s) =
      paritySectorSubmodule (sectorXi s) := by
  cases s
  · simpa [paritySectorSubmodule, sectorXi, Xi_unit_val, sectorXi_plusPlus] using Xi_unit_map_E_plus_plus
  · simpa [paritySectorSubmodule, sectorXi, Xi_unit_val, sectorXi_plusMinus] using Xi_unit_map_E_plus_minus
  · simpa [paritySectorSubmodule, sectorXi, Xi_unit_val, sectorXi_minusPlus] using Xi_unit_map_E_minus_plus
  · simpa [paritySectorSubmodule, sectorXi, Xi_unit_val, sectorXi_minusMinus] using Xi_unit_map_E_minus_minus

theorem unitForV4_map_paritySector (g : V4Group) (s : ParitySector) :
    Submodule.map (unitForV4 g : CoordEnd) (paritySectorSubmodule s) =
      paritySectorSubmodule (sectorPermutation g s) := by
  cases g
  · cases s <;>
      change Submodule.map (LinearMap.id : Coord →ₗ[ℝ] Coord) _ = _ <;>
      exact Submodule.map_id _
  · simpa [unitForV4, sectorPermutation] using C_unit_map_paritySector s
  · simpa [unitForV4, sectorPermutation] using Xi_unit_map_paritySector s
  · simpa [unitForV4, sectorPermutation] using Star_unit_map_paritySector s

theorem unitForV4Hom_map_paritySector (g : V4Group) (s : ParitySector) :
    Submodule.map ((unitForV4Hom g : CoordEndˣ) : CoordEnd)
        (paritySectorSubmodule s) =
      paritySectorSubmodule (sectorPermutation g s) := by
  change Submodule.map (unitForV4 g : CoordEnd) (paritySectorSubmodule s) = _
  exact unitForV4_map_paritySector g s

theorem unitForV4Hom_sector_transport_mul (g h : V4Group) (s : ParitySector) :
    Submodule.map ((unitForV4Hom (g * h) : CoordEndˣ) : CoordEnd)
        (paritySectorSubmodule s) =
      Submodule.map ((unitForV4Hom g : CoordEndˣ) : CoordEnd)
        (Submodule.map ((unitForV4Hom h : CoordEndˣ) : CoordEnd)
          (paritySectorSubmodule s)) := by
  rw [unitForV4Hom_map_paritySector (g * h) s]
  rw [unitForV4Hom_map_paritySector h s]
  rw [unitForV4Hom_map_paritySector g (sectorPermutation h s)]
  have hp : sectorPermutation (g * h) =
      sectorPermutation g * sectorPermutation h :=
    map_mul (sectorPermutationHom) g h
  rw [hp]
  rfl

end InfoGeometry.Canonical.CayleyDualitySectorPermutationConcreteBridge
