import Mathlib
import InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge
import InfoGeometry.Physics.Algebra.NPotentHorizonInvariantPacket

/-!
# Fibonacci braid instance of the general `N`-potent invariant packet

This is a concrete consumer of the generic `NPotentInvariantPacket` API.
It packages the two already-proved Fibonacci braid generators on the actual
tripotent ambient carrier.  No Hodge or modular operator is introduced here:
the action type contains only the two braid generators.
-/

noncomputable section

namespace InfoGeometry.Physics.Algebra.FibonacciNPotentInvariantPacketBridge

open InfoGeometry.Physics.Algebra
open InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge
open InfoGeometry.Canonical.NPotentOperatorEigenspaceBridge

/-- The two generators of the concrete Fibonacci braid packet. -/
def fibonacciBraidAction (a : Fin 2) : Module.End ℂ AmbientSpace :=
  if a = 0 then ambientBraidR else ambientBraidB

@[simp] theorem fibonacciBraidAction_zero :
    fibonacciBraidAction 0 = ambientBraidR := by
  simp [fibonacciBraidAction]

@[simp] theorem fibonacciBraidAction_one :
    fibonacciBraidAction 1 = ambientBraidB := by
  simp [fibonacciBraidAction]

/-- Concrete `N = 3` invariant packet carried by the Fibonacci braid sector. -/
def fibonacciBraidNPotentPacket : NPotentInvariantPacket AmbientSpace where
  N := 3
  N_ge_two := by norm_num
  T := horizonTripotent
  nPotent := horizonTripotent_is_tripotent
  action := Fin 2
  operator := fibonacciBraidAction
  commutes_zero := by
    intro a
    fin_cases a
    · simpa [fibonacciBraidAction, horizonProjZero,
        nPotentZeroProjector] using ambientBraidR_commutes_projZero
    · simpa [fibonacciBraidAction, horizonProjZero,
        nPotentZeroProjector] using ambientBraidB_commutes_projZero

theorem fibonacciBraidPacket_action_preserves_horizon (a : Fin 2) :
    ∀ x, x ∈ NPotentHorizonCarrier fibonacciBraidNPotentPacket →
      fibonacciBraidAction a x ∈ NPotentHorizonCarrier fibonacciBraidNPotentPacket :=
  nPotent_action_preserves_horizon fibonacciBraidNPotentPacket a

/-! The generic restricted-action API now exposes the concrete Fibonacci
braid relations without introducing a second horizon carrier. -/

theorem fibonacciBraidPacket_restricted_artin :
    nPotentRestrictedAction fibonacciBraidNPotentPacket (0 : Fin 2) *
          nPotentRestrictedAction fibonacciBraidNPotentPacket (1 : Fin 2) *
          nPotentRestrictedAction fibonacciBraidNPotentPacket (0 : Fin 2) =
        nPotentRestrictedAction fibonacciBraidNPotentPacket (1 : Fin 2) *
          nPotentRestrictedAction fibonacciBraidNPotentPacket (0 : Fin 2) *
          nPotentRestrictedAction fibonacciBraidNPotentPacket (1 : Fin 2) := by
  simpa using horizon_restricted_braid_artin

theorem fibonacciBraidPacket_restricted_noncommutative :
    nPotentRestrictedAction fibonacciBraidNPotentPacket (0 : Fin 2) *
          nPotentRestrictedAction fibonacciBraidNPotentPacket (1 : Fin 2) ≠
        nPotentRestrictedAction fibonacciBraidNPotentPacket (1 : Fin 2) *
          nPotentRestrictedAction fibonacciBraidNPotentPacket (0 : Fin 2) := by
  simpa using horizon_restricted_braid_noncommutative

end InfoGeometry.Physics.Algebra.FibonacciNPotentInvariantPacketBridge
