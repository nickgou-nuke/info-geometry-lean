/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.HodgeTheorems

/-! Transitive reachability alone does not determine whether a triangle is a
2-cell: the same 1-skeleton has different first homology when its face is
omitted. -/
namespace DAG.TransitiveTriangleHodgeCounterexample

/-- Keep the canonical triangle's graph and edges but omit its 2-cell. -/
def triangleWithoutFace : DAG.TwoComplex Nat :=
  { DAG.canonicalTriangleComplex with faces := #[] }

/-- The builder's transitive-triangle policy fills the cycle. -/
theorem builder_fills_transitive_triangle :
    DAG.canonicalTriangleComplex.faces.size = 1 ∧
      DAG.betti1 DAG.canonicalTriangleComplex = 0 := by
  native_decide

/-- The same vertices and edges, with no declared face, have one 1-cycle and
still satisfy the chain condition. -/
theorem omitting_face_preserves_cycle :
    DAG.betti1 triangleWithoutFace = 1 ∧
      DAG.boundarySquaredZero triangleWithoutFace = true := by
  native_decide

end DAG.TransitiveTriangleHodgeCounterexample
