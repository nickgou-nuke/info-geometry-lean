/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.CocycleBridge

/-!
# Finite Hodge readout for a `TwoComplex`

This module exposes the finite Hodge-data construction owned by
`DAG.CocycleBridge`. It does not construct an algebra-valued functor, a
colimit extension, or a continuous Connes-cocycle correspondence.
-/

namespace DAG.TwoComplexFunctor

open DAG

/-- The harmonic-coordinate component in the finite Hodge package is bounded
by the dimension of its edge-coordinate space. This is the nullity bound
encoded by `betti1Hodge = edges.size - gaussianRank(laplacian1)`. -/
theorem hodgeData_harmonicDimension_le_edgeCount
    {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (CocycleBridge.fromTwoComplex tc).hodgeDecomp.2.2 ≤ tc.edges.size := by
  change betti1Hodge tc ≤ tc.edges.size
  unfold betti1Hodge
  exact Nat.sub_le _ _

end DAG.TwoComplexFunctor
