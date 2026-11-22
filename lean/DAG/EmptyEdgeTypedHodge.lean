/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.EmptyEdgeArrayShapeCounterexample

/-! Dimension-indexed matrices preserve the vertex carrier when the edge
carrier is empty. This generalizes the isolated-three-vertices witness. -/
namespace DAG.EmptyEdgeTypedHodge

open DAG

variable {α : Type*} [BEq α] [Hashable α]

/-- With no indexed edges, the typed vertex Laplacian is zero for any number
of vertices. Its matrix shape remains indexed by the vertex carrier. -/
theorem typed_vertex_laplacian_zero_of_no_edges (tc : TwoComplex α)
    (hEdges : tc.edges.size = 0) :
    Matrix.transpose (boundary1Matrix tc) * boundary1Matrix tc = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro e he
  exact Fin.elim0 (hEdges ▸ e)

/-- The typed statement still applies to the existing isolated-vertex witness. -/
theorem isolatedVertices_typed_laplacian_zero :
    Matrix.transpose (boundary1Matrix
      DAG.EmptyEdgeArrayShapeCounterexample.isolatedVertices) *
      boundary1Matrix DAG.EmptyEdgeArrayShapeCounterexample.isolatedVertices = 0 :=
  typed_vertex_laplacian_zero_of_no_edges _ rfl

end DAG.EmptyEdgeTypedHodge
