import Mathlib.Tactic
import InfoGeometry.Canonical.PauliSignedPermutationSupergradedBridge
import InfoGeometry.Canonical.TrialitySpin8Permutations

/-!
# Coordinate/triality label intertwiner

This is the finite label-level bridge between the coordinate `Fin 3` cycle and
the abstract `vector`, `spinorPlus`, `spinorMinus` sector cycle.  It does not
identify the coordinate carrier with an eight-dimensional representation.
-/

namespace InfoGeometry.Canonical.CoordinateTrialityLabelIntertwiner

open InfoGeometry.Canonical.TrialitySpin8Permutations

abbrev ConformalNullPair :=
  InfoGeometry.Clifford.ConformalLift55.ConformalNullPair

abbrev Cl55 := InfoGeometry.Clifford.ConformalLift55.Cl55

abbrev Coordinate := Fin 3

def coordinateToSector : Coordinate → TrialitySector := id

def coordinateCycle : Equiv.Perm Coordinate := trialityCycle

def sectorTransport (s : TrialitySector) : TrialitySector :=
  trialityCycle s

def seedReadout (p : ConformalNullPair) : Coordinate → Cl55 :=
  fun c => trialitySectorSeed p (coordinateToSector c)

def transportedSeedReadout (p : ConformalNullPair) : Coordinate → Cl55 :=
  fun c => trialitySectorSeed p (coordinateToSector (coordinateCycle c))

theorem coordinate_sector_intertwining (c : Coordinate) :
    coordinateToSector (coordinateCycle c) =
      sectorTransport (coordinateToSector c) := by
  rfl

theorem seed_readout_intertwining
    (p : ConformalNullPair) (c : Coordinate) :
    transportedSeedReadout p c =
      seedReadout p (coordinateCycle c) := by
  rfl

theorem seed_readout_vector_to_spinorPlus
    (p : ConformalNullPair) :
    transportedSeedReadout p vectorSector =
      seedReadout p spinorPlusSector := by
  rfl

theorem seed_readout_spinorPlus_to_spinorMinus
    (p : ConformalNullPair) :
    transportedSeedReadout p spinorPlusSector =
      seedReadout p spinorMinusSector := by
  rfl

theorem seed_readout_spinorMinus_to_vector
    (p : ConformalNullPair) :
    transportedSeedReadout p spinorMinusSector =
      seedReadout p vectorSector := by
  rfl

theorem coordinate_triality_cycle_order_three (c : Coordinate) :
    coordinateCycle (coordinateCycle (coordinateCycle c)) = c := by
  change (trialityCycle ^ 3) c = c
  rw [trialityCycle_pow_three]
  rfl

end InfoGeometry.Canonical.CoordinateTrialityLabelIntertwiner
