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

/--
From a topological socket and external isometry premise, inherit the existing
information-preservation conjunction.
-/
theorem information_preservation_from_topological_socket {n : ℕ}
    (S : TopologicalSpinSocket n)
    (h_unitarity : S.inv.closure.moebiusParity.transpose * S.inv.closure.moebiusParity =
      S.inv.closure.I) :
    (S.inv.closure.moebiusParity.transpose * S.inv.closure.moebiusParity =
      S.inv.closure.I) ∧ (S.inv.closure.gromovWittenIndex = 0) := by
  constructor
  · exact h_unitarity
  · exact spin_socket_gw_zero S

/--
Inject spin-topological anomaly data into the finite globality packet pipeline.
-/
theorem anomaly_packet_from_topological_socket
    {M State Info : Type*}
    {n : ℕ}
    (S : TopologicalSpinSocket n)
    (G : ConformalFiveGradeSystem M)
    (A : GradeTwoInformationLedger State Info)
    (step : ℝ)
    (s : State)
    (k : ℕ)
    (chi_global_4 moebius_strip_4 : Matrix (Fin 4) (Fin 4) ℚ)
    (witten_parity_factor : ℕ → ℤ)
    (h_chi_global : Matrix.trace chi_global_4 = 0)
    (h_moebius_chiral : Matrix.trace (moebius_strip_4 * chi_global_4) = 0)
    (h_witten_parity :
      witten_parity_factor 1 + witten_parity_factor 2 +
      witten_parity_factor 3 + witten_parity_factor 4 = 0) :
    S.inv.closure.gromovWittenIndex = 0 ∧
    S.inv.closure.moebiusParity * S.inv.closure.moebiusParity = -S.inv.closure.I ∧
    (∀ x, x ∈ G.sourceSet ↔ G.theta x ∈ G.sinkSet) ∧
    (∀ x, x ∈ G.incomingSet ↔ G.theta x ∈ G.outgoingSet) ∧
    (∀ x, x ∈ G.centerSet ↔ G.theta x ∈ G.centerSet) ∧
    Matrix.trace chi_global_4 = 0 ∧
    Matrix.trace (moebius_strip_4 * chi_global_4) = 0 ∧
    witten_parity_factor 1 + witten_parity_factor 2 +
      witten_parity_factor 3 + witten_parity_factor 4 = 0 ∧
    (A.visible s - A.visible (stateAt A step s k) =
      A.gradeTwo (stateAt A step s k) - A.gradeTwo s) := by
  refine ⟨spin_socket_gw_zero S, spin_socket_ribbon_twist_eq_minus_id S, ?_⟩
  exact five_graded_mobius_witten_globality_packet G A step s k
    chi_global_4 moebius_strip_4 witten_parity_factor h_chi_global h_moebius_chiral h_witten_parity

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