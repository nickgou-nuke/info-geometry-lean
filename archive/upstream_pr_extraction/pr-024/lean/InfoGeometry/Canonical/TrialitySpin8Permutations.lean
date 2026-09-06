import Mathlib
import InfoGeometry.Canonical.Cl55V4SpinorFragmentation

-- File: TrialitySpin8Permutations.lean
-- Conservative boundary-level witness of a 3-cycle permutation on sector labels.
-- It formalizes the cycle 0 → 1 → 2 → 0 and transport of concrete Cl(5,5) seeds.

namespace InfoGeometry.Canonical.TrialitySpin8Permutations

open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Canonical.Cl55V4SpinorFragmentation

/-- Sector indices for the abstract three-way triality cycle. -/
abbrev TrialitySector := Fin 3

/-- Sector aliases used by the boundary vocabulary. -/
def vectorSector : TrialitySector := 0
def spinorPlusSector : TrialitySector := 1
def spinorMinusSector : TrialitySector := 2

/-- The triality 3-cycle `0 → 1 → 2 → 0` on sector labels.

`Fin.cycleRange` with `Fin.last 2 : Fin 3` gives exactly this cycle.
-/
def trialityCycle : Equiv.Perm TrialitySector :=
  Fin.cycleRange (n := 3) (Fin.last 2)

@[simp] theorem trialityCycle_vector :
    trialityCycle vectorSector = spinorPlusSector := by
  decide

@[simp] theorem trialityCycle_spinorPlus :
    trialityCycle spinorPlusSector = spinorMinusSector := by
  decide

@[simp] theorem trialityCycle_spinorMinus :
    trialityCycle spinorMinusSector = vectorSector := by
  decide

@[simp] theorem trialityCycle_pow_three :
    trialityCycle ^ 3 = (1 : Equiv.Perm TrialitySector) := by
  ext i
  fin_cases i <;> decide

/-- Three distinguished `Cl(5,5)` sector seeds used as triality labels.

`vector` is chosen as the commutator seed, while the two spinor sectors are
`u ± v` combinations already developed in `Cl55V4SpinorFragmentation`.
-/
def trialitySectorSeed (p : ConformalNullPair) : TrialitySector → Cl55 :=
  Fin.cases
    (p.u * p.v - p.v * p.u)
    (Fin.cases
      (p.u + p.v)
      (fun _ => p.u - p.v))

@[simp] theorem trialitySectorSeed_vector (p : ConformalNullPair) :
    trialitySectorSeed p vectorSector = p.u * p.v - p.v * p.u := by
  rfl

@[simp] theorem trialitySectorSeed_spinorPlus (p : ConformalNullPair) :
    trialitySectorSeed p spinorPlusSector = p.u + p.v := by
  rfl

@[simp] theorem trialitySectorSeed_spinorMinus (p : ConformalNullPair) :
    trialitySectorSeed p spinorMinusSector = p.u - p.v := by
  rfl

/-- `trialitySectorTransport` applies the formal 3-cycle to the sector label. -/
def trialitySectorTransport (p : ConformalNullPair) (s : TrialitySector) : Cl55 :=
  trialitySectorSeed p (trialityCycle s)

theorem trialitySectorTransport_cycle :
    trialityCycle (trialityCycle (trialityCycle (0 : TrialitySector))) = 0 := by
  decide

theorem trialitySectorTransport_vector_to_spinorPlus (p : ConformalNullPair) :
    trialitySectorTransport p vectorSector = trialitySectorSeed p spinorPlusSector := by
  rfl

theorem trialitySectorTransport_spinorPlus_to_spinorMinus (p : ConformalNullPair) :
    trialitySectorTransport p spinorPlusSector = trialitySectorSeed p spinorMinusSector := by
  rfl

theorem trialitySectorTransport_spinorMinus_to_vector (p : ConformalNullPair) :
    trialitySectorTransport p spinorMinusSector = trialitySectorSeed p vectorSector := by
  rfl

/-- The transport is a genuine 3-cycle on sector labels:
applying it three times returns each seed. -/
theorem trialitySectorTransport_cube_id (p : ConformalNullPair) (s : TrialitySector) :
    trialitySectorSeed p ((trialityCycle ^ 3) s) = trialitySectorSeed p s := by
  simp [trialityCycle_pow_three]

end InfoGeometry.Canonical.TrialitySpin8Permutations
