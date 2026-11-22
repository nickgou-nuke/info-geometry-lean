/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.SelfLoopIncidenceRegression
import DAG.GraphHodge

/-! A vertex sign assignment is compatible with the extended cell grading only
when each nonzero incidence edge joins equal signs. -/
namespace DAG.VertexEdgeChiralityCounterexample

open DAG.SelfLoopIncidenceRegression

def oneEdge : DAG.TwoComplex Nat :=
  { oneLoop with
    base := { oneLoop.base with
      toGraph := { oneLoop.base.toGraph with
        nodes := #[0, 1]
        forward := #[#[(1, DAG.EdgeKind.type)], #[]] } }
    edges := #[(0, 1)] }

def oppositeEndpointSigns : DAG.ChiralGrading 2 :=
  DAG.ChiralGrading.ofBool 2 (fun i => i == 0)

/-- The source/sink labeling fails anticommutation on the single oriented edge. -/
theorem source_sink_grading_not_chiral :
    DAG.chiralAnticommutes oneEdge oppositeEndpointSigns = false := by
  native_decide

/-- The edge-target entry of `ΓD + DΓ` is exactly `-2`. -/
theorem target_edge_anticommutator_entry :
    (((DAG.matAdd
      (DAG.matMul (DAG.extendedChiralGrading oneEdge oppositeEndpointSigns)
        (DAG.graphDirac oneEdge))
      (DAG.matMul (DAG.graphDirac oneEdge)
        (DAG.extendedChiralGrading oneEdge oppositeEndpointSigns)))[2]!)[1]!) = -2 := by
  native_decide

end DAG.VertexEdgeChiralityCounterexample
