/- 
InfoGeometry/Algebraic/NarainSupervolumeBridgeData.lean

Proof-carrying bridge between the split Narain charge lattice, the orthogonal
core, and the supervolume readout.

This file does not prove a concrete lattice-sum formula. It packages the data
needed for a later theta/supervolume theorem:

* finite state space;
* Narain charge assignment;
* realification into the split carrier;
* orthogonal charge symmetries;
* a readout equality between lattice sum and supervolume;
* a negative-log effective action.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebraic.NarainOrthogonalCore
import InfoGeometry.Algebraic.NarainRealification
import InfoGeometry.Algebraic.SplitSuperGeometry

noncomputable section

open scoped BigOperators
open InfoGeometry.Algebraic.Split

namespace InfoGeometry.Algebraic.SplitSignature

/--
Bridge data for a finite Narain charge spectrum and its supervolume readout.

The state space and charge assignment are intentionally abstract.  The bridge
only records the compatibility data needed by later theta/lattice-sum theorems.
-/
structure NarainSupervolumeBridgeData (n : ℕ) where
  State : Type
  fintypeState : Fintype State
  decidableEqState : DecidableEq State

  /-- Discrete Narain charge carried by each state. -/
  charge : State → NarainCharge n

  /-- Realified split charge used by the geometric readout. -/
  realifiedCharge : State → SplitModule n

  /-- Compatibility of the realified charge with the Narain realification map. -/
  realifiedCharge_eq : ∀ s : State, realifiedCharge s = narainRealification (charge s)

  /-- Parity on the finite state space. -/
  parity : State → ℤ

  /-- The lattice-sum / partition readout. -/
  latticeSumReadout : ℝ

  /-- The supervolume readout paired with the lattice sum. -/
  supervolumeReadout : ℝ

  /-- Positivity gate for the logarithmic potential. -/
  supervolume_pos : 0 < supervolumeReadout

  /-- The lattice sum is the same readout as the supervolume. -/
  latticeSumReadout_eq_supervolumeReadout : latticeSumReadout = supervolumeReadout

  /-- Negative-log effective action attached to the supervolume. -/
  effectiveAction : ℝ

  /-- The effective action is the negative log of the supervolume readout. -/
  effectiveAction_eq_negLog_supervolumeReadout :
    effectiveAction = - Real.log supervolumeReadout

  /-- Orthogonal symmetry core acting on the Narain charge data. -/
  orthogonalCore : NarainOrthogonalCore n

namespace NarainSupervolumeBridgeData

variable {n : ℕ}

/-- The readout used for the lattice sum. -/
def latticeSum (D : NarainSupervolumeBridgeData n) : ℝ :=
  D.latticeSumReadout

/-- The readout used for the supervolume. -/
def supervolume (D : NarainSupervolumeBridgeData n) : ℝ :=
  D.supervolumeReadout

/-- The negative-log effective action. -/
def negativeLogPotential (D : NarainSupervolumeBridgeData n) : ℝ :=
  D.effectiveAction

@[simp]
theorem latticeSum_eq_supervolume
    (D : NarainSupervolumeBridgeData n) :
    D.latticeSum = D.supervolume := by
  simpa [latticeSum, supervolume] using D.latticeSumReadout_eq_supervolumeReadout

@[simp]
theorem effectiveAction_eq_negLog
    (D : NarainSupervolumeBridgeData n) :
    D.negativeLogPotential = - Real.log D.supervolume := by
  simpa [negativeLogPotential, supervolume] using D.effectiveAction_eq_negLog_supervolumeReadout

end NarainSupervolumeBridgeData

end InfoGeometry.Algebraic.SplitSignature
