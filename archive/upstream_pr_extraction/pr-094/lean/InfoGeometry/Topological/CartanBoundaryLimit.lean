/-
InfoGeometry/Topological/CartanBoundaryLimit.lean

Generic boundary limits for Cartan symmetric spaces.
No complex imports.
-/

import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import InfoGeometry.Algebraic.CartanCocycle

noncomputable section

namespace InfoGeometry.Topological.Cartan

open Filter
open scoped Topology

/--
A boundary approach to a Cartan compactification, cusp, isotropic flag, or
decompactification regime.
-/
structure CartanBoundaryApproach
    (P X : Type*)
    [TopologicalSpace X] where
  baseFilter : Filter P
  point : P → X

/--
Boundary anomaly as a filter limit of a cocycle.

This is the generic rank-independent limit statement used by both Cartan
towers.
-/
def boundaryCocycleLimit
    {G X R P : Type*}
    [Group G] [MulAction G X]
    [TopologicalSpace X]
    [Group R] [TopologicalSpace R]
    (C : InfoGeometry.Algebraic.Cartan.CartanRotorCocycle G X R)
    (g : G)
    (approach : CartanBoundaryApproach P X)
    (anomaly : R) : Prop :=
  Tendsto
    (fun p : P => C g (approach.point p))
    approach.baseFilter
    (𝓝 anomaly)

end InfoGeometry.Topological.Cartan
