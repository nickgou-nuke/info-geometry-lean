/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState

/-!
# Cyclic trace transport for the concrete C⋆ matrix tower

The finite C⋆ trace-state owner already proves normalized positivity and
compatibility of the state family.  This closure records the stronger
coherence statement needed by tracial/KMS consumers: multiplication may be
performed after transport to any later stage, and the state readout agrees
with the original-stage cyclic readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower

theorem cstarMatrixTraceFunctional_transition_cyclic
    {i j : ℕ} (hij : i ≤ j)
    (A B : CStarMatrixStage i) :
    cstarMatrixTraceFunctional j
        (cstarConcreteMap hij A * cstarConcreteMap hij B) =
      cstarMatrixTraceFunctional i (A * B) ∧
    cstarMatrixTraceFunctional j
        (cstarConcreteMap hij A * cstarConcreteMap hij B) =
      cstarMatrixTraceFunctional j
        (cstarConcreteMap hij B * cstarConcreteMap hij A) := by
  constructor
  · have hmul : cstarConcreteMap hij (A * B) =
        cstarConcreteMap hij A * cstarConcreteMap hij B :=
      (cstarConcreteMap hij).map_mul A B
    have htrans : cstarMatrixTraceFunctional j (cstarConcreteMap hij (A * B)) =
        cstarMatrixTraceFunctional i (A * B) := by
      simpa [cstarMatrixTraceState, cstarMatrixTraceFunctional] using
        (cstarMatrixTraceState_transition_general hij (A * B))
    exact (congrArg (fun X => cstarMatrixTraceFunctional j X) hmul).symm.trans
      htrans
  · have hmulAB : cstarConcreteMap hij (A * B) =
        cstarConcreteMap hij A * cstarConcreteMap hij B :=
      (cstarConcreteMap hij).map_mul A B
    have hmulBA : cstarConcreteMap hij (B * A) =
        cstarConcreteMap hij B * cstarConcreteMap hij A :=
      (cstarConcreteMap hij).map_mul B A
    have hcyc : cstarMatrixTraceFunctional i (A * B) =
        cstarMatrixTraceFunctional i (B * A) := by
      rw [cstarMatrixTraceFunctional_apply, cstarMatrixTraceFunctional_apply,
        map_mul, map_mul, matrixTraceState_mul_comm]
    have htransAB : cstarMatrixTraceFunctional j (cstarConcreteMap hij (A * B)) =
        cstarMatrixTraceFunctional i (A * B) := by
      simpa [cstarMatrixTraceState, cstarMatrixTraceFunctional] using
        (cstarMatrixTraceState_transition_general hij (A * B))
    have htransBA : cstarMatrixTraceFunctional j (cstarConcreteMap hij (B * A)) =
        cstarMatrixTraceFunctional i (B * A) := by
      simpa [cstarMatrixTraceState, cstarMatrixTraceFunctional] using
        (cstarMatrixTraceState_transition_general hij (B * A))
    exact ((congrArg (fun X => cstarMatrixTraceFunctional j X) hmulAB).symm.trans
      htransAB).trans hcyc |>.trans htransBA.symm |>.trans
      (congrArg (fun X => cstarMatrixTraceFunctional j X) hmulBA)

end InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
