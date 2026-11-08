/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Projective.HorizonInformationScrambling
import InfoGeometry.Projective.KasparovKreinDIIIBridge
import InfoGeometry.Projective.AndreevHorizonUnitarity

/-!
# InfoGeometry.Projective.FibonacciMZMBraidingBridge

Finite Fibonacci/MZM braid readout bridge.

This file records two conservative readback lemmas:

1. **Rewrite-invariant Fibonacci projective gate**: any phase assignment
   invariant under the adjacent braid rewrite `[i, i+1, i] ~ [i+1, i, i+1]`
   yields a projective Fibonacci gate invariant under the same rewrite.
   Direct readback from `FiniteFibonacciAnyonBraiding`.

2. **DIII/Andreev finite braid packet**: a supplied `ModularTimeFlow` plus
   state yields `IsUnitaryBraiding ∧ InformationIsConserved`.
   Direct readback from `HorizonInformationScrambling.finite_unitary_braiding_packet`.

No braid-group representation, no fast-scrambling bound, no physical MZM
protection theorem is claimed here. These are finite algebraic readbacks only.
-/

namespace InfoGeometry.Projective.FibonacciMZMBraidingBridge

open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Projective.Scrambling
open InfoGeometry.Projective.AndreevHorizonUnitarity

/-- A Fibonacci/MZM phase readout.

Packages a braid-phase assignment, a gate readout, and the explicit
phase-invariance hypothesis under the adjacent braid rewrite.
-/
structure FibonacciMZMReadout (Gate : Type*) [SMul (Units ℂ) Gate] where
  phase : FibonacciBraidPhase
  readout : Equiv.Perm ℕ → Gate
  braidPhase_rewrite :
    ∀ (i : ℕ) (left right : FibonacciBraidWord),
      phase (left ++ [i, i + 1, i] ++ right) =
        phase (left ++ [i + 1, i, i + 1] ++ right)

/-- Rewrite-invariant Fibonacci projective gate readback.

If the phase is invariant under the adjacent braid rewrite, so is the
projective Fibonacci gate. Direct readback from
`FiniteFibonacciAnyonBraiding.fibonacciProjectiveGate_braid_rewrite_of_phase`.
-/
theorem fibonacci_mzm_projective_gate_braid_rewrite
    {Gate : Type*} [SMul (Units ℂ) Gate]
    (D : FibonacciMZMReadout Gate)
    (i : ℕ) (left right : FibonacciBraidWord) :
    fibonacciProjectiveGate Gate D.phase D.readout
      (left ++ [i, i + 1, i] ++ right) =
    fibonacciProjectiveGate Gate D.phase D.readout
      (left ++ [i + 1, i, i + 1] ++ right) := by
  exact fibonacciProjectiveGate_braid_rewrite_of_phase Gate D.phase D.readout i left right
    (D.braidPhase_rewrite i left right)

/-- A DIII/Andreev-to-Fibonacci finite braid packet.

Packages a supplied unitary braiding flow, a state, and an Andreev state.
The `parityMatchesBraid` field is intentionally left as a bare `Prop` to be
instantiated by future owners who construct an explicit DIII-to-Fibonacci
label map.
-/
structure DIIIAndreevFibonacciPacket (n : ℕ) where
  flow : ModularTimeFlow n
  state : HorizonMicrostates n
  andreevState : InfallingParticle
  parityMatchesBraid : Prop

/-- DIII/Andreev finite braid packet readback.

Reads back `IsUnitaryBraiding ∧ InformationIsConserved` directly from
`HorizonInformationScrambling.finite_unitary_braiding_packet`. This proves only
that the supplied flow and state satisfy the conservation equation; it does
not imply braid density, fast scrambling, or protected Majorana modes.
-/
theorem diii_andreev_fibonacci_packet_readback {n : ℕ}
    (P : DIIIAndreevFibonacciPacket n) :
    IsUnitaryBraiding P.flow ∧ InformationIsConserved P.flow P.state := by
  exact finite_unitary_braiding_packet P.flow P.state

end InfoGeometry.Projective.FibonacciMZMBraidingBridge
