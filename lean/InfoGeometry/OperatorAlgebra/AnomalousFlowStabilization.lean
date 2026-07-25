/-
InfoGeometry/OperatorAlgebra/AnomalousFlowStabilization.lean

Anomalous flow stabilization sockets.

This file records the model-level witness saying that a nonzero anomaly/readout
and a protected topological charge force a stable non-flat representative.  It
does not claim that Clifford kinematics alone prove a tubule phase.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AnomalousFlowStabilization

/-! ## 1. Stabilization witness -/

/--
Witness data for anomalous-flow stabilization.

The intended reading is:

`local Clifford shear + anomalous/modular flow + protected charge`
forces existence of a stable non-flat representative in the model.
-/
structure AnomalousFlowStabilizationWitness
    (Op State : Type*) [Ring Op] where
  /-- Admissible flow on states. -/
  flow : ℝ → State → State

  /-- Anomaly/residue/readout attached to states. -/
  anomalyReadout : State → ℝ

  /-- Topological charge, index, or winding readout. -/
  topologicalCharge : State → ℤ

  /-- The topological charge is preserved by the admissible flow. -/
  charge_invariant_under_flow :
    ∀ (t : ℝ) (x : State),
      topologicalCharge (flow t x) = topologicalCharge x

  /-- Flat/trivial vacuum predicate. -/
  flat_vacuum : State → Prop

  /-- Stable non-flat representative predicate. -/
  nonflat_stable : State → Prop

  /--
  Model certificate: nonzero anomaly and nonzero topological charge force a
  stable non-flat representative.
  -/
  anomaly_forces_stable_nonflat :
    ∀ x : State,
      anomalyReadout x ≠ 0 →
      topologicalCharge x ≠ 0 →
        ∃ y : State, nonflat_stable y

namespace AnomalousFlowStabilizationWitness

variable {Op State : Type*} [Ring Op]
variable (W : AnomalousFlowStabilizationWitness Op State)

/-- Re-export conservation of topological charge under the flow. -/
theorem charge_preserved
    (t : ℝ)
    (x : State) :
    W.topologicalCharge (W.flow t x) = W.topologicalCharge x :=
  W.charge_invariant_under_flow t x

/-- Re-export the stable non-flat representative certificate. -/
theorem stable_nonflat_of_anomaly_and_charge
    {x : State}
    (hanom : W.anomalyReadout x ≠ 0)
    (hcharge : W.topologicalCharge x ≠ 0) :
    ∃ y : State, W.nonflat_stable y :=
  W.anomaly_forces_stable_nonflat x hanom hcharge

end AnomalousFlowStabilizationWitness

end InfoGeometry.OperatorAlgebra.AnomalousFlowStabilization
