import Mathlib.Tactic
import InfoGeometryCore.Basic
import InfoGeometry.Physics.ElectronParafermionFlow
import InfoGeometry.Algebra.PeirceLadderOperators

/-!
# Tripotent index map into a three-slot ladder packet

This module contains only a finite bookkeeping map from the three
`TripotentState` values to `Fin 3`, plus the corresponding cyclicity and integer
balance readouts.  It does not prove a Standard Model representation theorem,
SU(3) color emergence, or a physical topological-origin theorem.
-/

namespace InfoGeometry.Physics

open InfoGeometryCore
open InfoGeometry.Algebra.PeirceLadder

/-- 
A finite index map from the three tripotent states to `Fin 3`.
-/
def tripotentStateIndex : TripotentState → Fin 3
  | .neg  => 0 -- Red / down-curvature
  | .zero => 1 -- Green / flat-curvature
  | .pos  => 2 -- Blue / up-curvature

/--
The triality cycle increments the finite index modulo three.
-/
theorem tripotent_state_index_cycle (s : TripotentState) :
    (tripotentStateIndex (TripotentState.trialityCycle s)).val =
    (tripotentStateIndex s + 1) % 3 := by
  cases s <;> rfl

/-- 
Select a ladder-packet generator using the finite tripotent index.
-/
def instantiateLadderFromTripotentState
    (packet : QuarkLadderPacket) 
    (s : TripotentState) : CliffordAlgebra Cl11Fermions.q11 :=
  packet.alpha (tripotentStateIndex s)

/--
Integer balance readout for the `+1` and `-1` tripotent values.
-/
theorem balanced_tripotent_integer_sum_zero (F5 F7 : ℤ) (h_balance : F5 = F7) :
    (F5 * (TripotentState.toInt TripotentState.pos) + 
     F7 * (TripotentState.toInt TripotentState.neg)) = 0 := by
  dsimp [TripotentState.toInt]
  omega

end InfoGeometry.Physics
