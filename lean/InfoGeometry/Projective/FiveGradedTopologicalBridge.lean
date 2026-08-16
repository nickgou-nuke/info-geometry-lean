import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.FiveGradedMobiusWittenGlobality
import InfoGeometry.Projective.FiveGradedTopologicalInvariants
import InfoGeometry.Projective.BlackHoleUnitarityBridge

/-!
# Five-Graded Topological Bridge

This module packages the finite topological invariants into reusable
`sockets` for the black-hole / five-graded anomaly-flow side of the stack.

The package is deliberately conservative: it does not add analytical claims,
geometric realizability, or physical unitarity theorems. It records only the
finite preconditions and re-exports derived consequences already available in the
core closure and unitarity interfaces.
-/

namespace InfoGeometry.Projective.Topology

open InfoGeometry.Projective.Closure
open InfoGeometry.Canonical.Globality
open InfoGeometry.Projective.Unitarity

/--
A topological anomaly socket for the 5-graded closure layer.

Fields are finite, explicit premises intended for later module integration.
-/
structure TopologicalSpinSocket (n : ℕ) where
  /-- The stored 5-graded topological invariant packet. -/
  inv : SpinTopologicalInvariants n

  /-- Local anomaly trace must vanish (the Atiyah--Singer/pontryagin readout condition). -/
  parity_trace_zero : Matrix.trace inv.closure.moebiusParity = 0

  /-- Explicit marker that the global spinor obstruction is absent in this readout lane. -/
  spinor_ready : SpinStructureUnobstructed inv

/-- Spin bundle readiness is equivalent to `w2_obstruction = false` by definition. -/
 theorem spinor_bundle_ready {n : ℕ} (S : TopologicalSpinSocket n) :
  SpinStructureUnobstructed S.inv :=
  S.spinor_ready

/--
The closure Gromov--Witten scalar vanishes in the socket.
-/
theorem spin_socket_gw_zero {n : ℕ} (S : TopologicalSpinSocket n) :
    S.inv.closure.gromovWittenIndex = 0 := by
  rw [S.inv.closure.gw_eq_trace, S.parity_trace_zero]

/--
The stored Möbius parity still satisfies the topological ribbon identity.
-/
theorem spin_socket_ribbon_twist_eq_minus_id {n : ℕ} (S : TopologicalSpinSocket n) :
    S.inv.closure.moebiusParity * S.inv.closure.moebiusParity = -S.inv.closure.I := by
  simpa [ribbonTwist] using (ribbon_twist_eq_minus_id n S.inv)

/--
Upgrade to the existing black-hole horizon socket once explicit real-isometry is
supplied externally.
-/
def horizonS_of_topological_socket {n : ℕ}
    (S : TopologicalSpinSocket n)
    (h_unitarity : S.inv.closure.moebiusParity.transpose * S.inv.closure.moebiusParity =
      S.inv.closure.I) :
    HorizonSMatrix n :=
  { closure := S.inv.closure, unitarity := h_unitarity }

/-
The two information-preservation readouts are exposed separately so downstream
users do not have to unpack a conjunction wrapper.
-/
theorem topological_socket_unitarity {n : ℕ}
    (S : TopologicalSpinSocket n)
    (h_unitarity : S.inv.closure.moebiusParity.transpose * S.inv.closure.moebiusParity =
      S.inv.closure.I) :
    S.inv.closure.moebiusParity.transpose * S.inv.closure.moebiusParity =
      S.inv.closure.I :=
  h_unitarity

theorem topological_socket_gw_zero {n : ℕ}
    (S : TopologicalSpinSocket n)
    (_h_unitarity : S.inv.closure.moebiusParity.transpose * S.inv.closure.moebiusParity =
      S.inv.closure.I) :
    S.inv.closure.gromovWittenIndex = 0 :=
  spin_socket_gw_zero S

/-- A ready-made concrete property from the finite `2×2` Möbius model. -/
def concreteTopologicalSocket2 : TopologicalSpinSocket 2 :=
  { inv := concreteSpinTopologicalInvariants2
    parity_trace_zero := by
      simpa using (concrete_pontryagin_trace_zero)
    spinor_ready := by
      rfl }

/-- The concrete `2×2` socket has spin bundle readiness explicitly. -/
theorem concreteTopologicalSocket2_ready :
    SpinStructureUnobstructed concreteTopologicalSocket2.inv :=
  concreteTopologicalSocket2.spinor_ready

/-- The concrete `2×2` socket closes the local anomaly block. -/
theorem concreteTopologicalSocket2_gw_zero :
    concreteTopologicalSocket2.inv.closure.gromovWittenIndex = 0 :=
  spin_socket_gw_zero concreteTopologicalSocket2

end InfoGeometry.Projective.Topology
