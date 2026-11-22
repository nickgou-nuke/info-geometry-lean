/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.TwoComplex
import Mathlib.Tactic

namespace DAG.SelfLoopBoundaryCounterexample

/-- The executable array boundary and the dimension-indexed matrix boundary
agree entrywise on every valid edge and vertex index. -/
theorem array_boundary_entry_eq_matrix
    {α : Type} [BEq α] [Hashable α] (tc : DAG.TwoComplex α)
    (i : Fin tc.edges.size) (j : Fin tc.base.toGraph.nodes.size) :
    ((DAG.boundary1 tc)[i.val]!)[j.val]! = DAG.boundary1Matrix tc i j := by
  simp [DAG.boundary1, DAG.boundary1Matrix, DAG.incidenceBoundaryCoeff]

/-- Consequently each loop contributes the zero row to the array boundary. -/
theorem array_boundary_loop_entry_zero
    {α : Type} [BEq α] [Hashable α] (tc : DAG.TwoComplex α)
    (i : Fin tc.edges.size) (j : Fin tc.base.toGraph.nodes.size)
    (hloop : (tc.edges[i.val]).1 = (tc.edges[i.val]).2) :
    ((DAG.boundary1 tc)[i.val]!)[j.val]! = 0 := by
  rw [array_boundary_entry_eq_matrix]
  exact DAG.boundary1Matrix_self_loop_entry_zero tc i j hloop

end DAG.SelfLoopBoundaryCounterexample
