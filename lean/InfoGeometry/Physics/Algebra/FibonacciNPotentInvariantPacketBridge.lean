import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge
import InfoGeometry.Physics.Algebra.NPotentHorizonInvariantPacket

/-!
# Fibonacci braid instance of the general `N`-potent invariant packet

This is a concrete consumer of the generic `NPotentInvariantData` API.
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
def fibonacciBraidNPotentData : NPotentInvariantData AmbientSpace where
  N := 3
  T := horizonTripotent
  action := Fin 2
  operator := fibonacciBraidAction

theorem fibonacciBraidNPotentData_laws :
    NPotentInvariantDataLaws fibonacciBraidNPotentData := by
  change 2 ≤ 3 ∧ IsNPotent 3 horizonTripotent ∧
    (∀ a : Fin 2,
      fibonacciBraidAction a * (1 - horizonTripotent ^ 2) =
        (1 - horizonTripotent ^ 2) * fibonacciBraidAction a)
  refine ⟨by norm_num, horizonTripotent_is_tripotent, ?_⟩
  intro a
  fin_cases a
  · simpa [fibonacciBraidAction, horizonProjZero,
      nPotentZeroProjector] using ambientBraidR_commutes_projZero
  · simpa [fibonacciBraidAction, horizonProjZero,
      nPotentZeroProjector] using ambientBraidB_commutes_projZero

/-! The generic restricted-action API now exposes the concrete Fibonacci
braid relations without introducing a second horizon carrier. -/

theorem fibonacciBraidPacket_restricted_artin :
    nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (0 : Fin 2) *
        nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (1 : Fin 2) *
        nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (0 : Fin 2) =
      nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (1 : Fin 2) *
        nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (0 : Fin 2) *
        nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (1 : Fin 2) := by
  simpa using horizon_restricted_braid_artin

theorem fibonacciBraidPacket_restricted_noncommutative :
    nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (0 : Fin 2) *
        nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (1 : Fin 2) ≠
      nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (1 : Fin 2) *
        nPotentRestrictedAction fibonacciBraidNPotentData
          fibonacciBraidNPotentData_laws (0 : Fin 2) := by
  simpa using horizon_restricted_braid_noncommutative

end InfoGeometry.Physics.Algebra.FibonacciNPotentInvariantPacketBridge
