/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Physics.MatrixTraceBimodulePairingNative

/-!
# Trace-Pairing Invariance under Modular Flow

This module proves that the finite trace pairing on matrix/operator carriers
is infinitesimally ad-invariant under the modular flow generator K.
-/

open scoped Matrix
open InfoGeometry.Physics

namespace InfoGeometry.Volume.TracePairingModularInvariance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 🏆 THEOREM 1: Infinitesimal ad-invariance: Tr([K, X] Y) + Tr(X [K, Y]) = 0. -/
theorem infinitesimal_trace_pairing_ad_invariant (K X Y : TraceOperatorSpace n) :
    tracePairingNative (commutatorActionNative K X) Y +
    tracePairingNative X (commutatorActionNative K Y) = 0 := by
  rw [commutator_tracePairing_native K X Y, neg_add_cancel]

/-- 🏆 THEOREM 2: Generator orthogonality: Tr(K [K, X]) = 0. -/
theorem generator_trace_pairing_orthogonal (K X : TraceOperatorSpace n) :
    tracePairingNative K (commutatorActionNative K X) = 0 :=
  commutator_tracePairing_energyOrthogonal K X

end InfoGeometry.Volume.TracePairingModularInvariance
