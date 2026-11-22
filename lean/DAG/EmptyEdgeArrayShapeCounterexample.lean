/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.SelfLoopIncidenceRegression
import DAG.GraphHodge
import Mathlib.Tactic

/-! The array representation loses the vertex dimension when the edge array is empty;
the dimension-indexed matrix formulation retains it. -/
namespace DAG.EmptyEdgeArrayShapeCounterexample

open SelfLoopIncidenceRegression

/-- Three isolated vertices and no edges, faces, or digons. -/
def isolatedVertices : TwoComplex Nat :=
  { oneLoop with
    base := { oneLoop.base with
      toGraph := { oneLoop.base.toGraph with
        nodes := #[0, 1, 2]
        forward := #[] } }
    edges := #[]
    faces := #[]
    digons := #[] }

/-- The generic array transpose cannot infer three columns from zero edge rows,
so the array Laplacian has shape `0 × 0` rather than `3 × 3`. -/
theorem array_laplacian0_loses_vertex_shape :
    DAG.laplacian0 isolatedVertices = #[] := by
  native_decide

/-- The typed incidence Laplacian retains its actual vertex carrier and is the
zero endomorphism on the three isolated vertices. -/
theorem typed_laplacian0_is_zero :
    Matrix.transpose (DAG.boundary1Matrix isolatedVertices) *
      DAG.boundary1Matrix isolatedVertices = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact Fin.elim0 (by simpa [isolatedVertices] using k)

end DAG.EmptyEdgeArrayShapeCounterexample
