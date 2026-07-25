/-
InfoGeometry/OperatorAlgebra/SelfDualChiralConeBoundary.lean

Self-dual chiral cone boundary socket.

This module formalizes a narrow Operator-Erlangen reading of the phrase:

  boundary of the self-dual chiral cones / symmetric Cartan spaces.

It records:

* a cone and dual cone, related by an explicit self-duality law;
* a boundary predicate;
* a closure involution exchanging left/right chiral charts;
* boundary preservation under closure;
* the fixed-boundary equalizer as the survivor.

It does not identify the fixed boundary with a center, horizon, winding number,
BPS charge, natural cone, or Shilov boundary unless a separate model supplies
that witness.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ClosureInvolution
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SelfDualChiralConeBoundary

open ClosureInvolution

set_option linter.dupNamespace false

/-! ## 1. Self-dual chiral cone boundary datum -/

/--
A witness-gated self-dual chiral cone boundary.

`cone = dualCone` records self-duality at the level of the chosen model.
`boundaryOf` is the horizon/boundary predicate. The closure involution exchanges
left and right chiral charts and preserves the boundary.
-/
structure SelfDualChiralConeBoundary
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The chosen cone of positive/admissible states. -/
  cone : Set V

  /-- The model's dual cone. -/
  dualCone : Set V

  /-- Self-duality law for the cone. -/
  self_dual :
    cone = dualCone

  /-- Boundary/horizon predicate for the cone or associated domain. -/
  boundaryOf :
    V → Prop

  /-- Closure/Cartan/Mobius/Tomita involution. -/
  closure :
    LinearClosureInvolution V

  /-- Left chiral/projective chart. -/
  leftChart :
    Set V

  /-- Right chiral/projective chart. -/
  rightChart :
    Set V

  /-- Closure sends the left chart into the right chart. -/
  closure_maps_left_to_right :
    ∀ x : V, x ∈ leftChart → closure.theta x ∈ rightChart

  /-- Closure sends the right chart into the left chart. -/
  closure_maps_right_to_left :
    ∀ x : V, x ∈ rightChart → closure.theta x ∈ leftChart

  /-- Boundary is preserved by closure. -/
  boundary_preserved :
    ∀ x : V, boundaryOf x → boundaryOf (closure.theta x)

namespace SelfDualChiralConeBoundary

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (B : SelfDualChiralConeBoundary V)

/-- The supplied self-duality law is available. -/
theorem cone_eq_dualCone :
    B.cone = B.dualCone :=
  B.self_dual

/-- Closure reflects boundary membership backwards, by involutivity. -/
theorem boundary_preserved_reverse
    {x : V}
    (hx : B.boundaryOf (B.closure.theta x)) :
    B.boundaryOf x := by
  have h := B.boundary_preserved (B.closure.theta x) hx
  simpa [B.closure.theta_involutive x] using h

/-- Closure maps left-chart boundary data to right-chart boundary data. -/
theorem left_boundary_maps_to_right_boundary
    {x : V}
    (hleft : x ∈ B.leftChart)
    (hboundary : B.boundaryOf x) :
    B.closure.theta x ∈ B.rightChart ∧
      B.boundaryOf (B.closure.theta x) :=
  ⟨B.closure_maps_left_to_right x hleft,
    B.boundary_preserved x hboundary⟩

/-- Closure maps right-chart boundary data to left-chart boundary data. -/
theorem right_boundary_maps_to_left_boundary
    {x : V}
    (hright : x ∈ B.rightChart)
    (hboundary : B.boundaryOf x) :
    B.closure.theta x ∈ B.leftChart ∧
      B.boundaryOf (B.closure.theta x) :=
  ⟨B.closure_maps_right_to_left x hright,
    B.boundary_preserved x hboundary⟩

/--
Closure-fixed boundary points.

This is the fixed equalizer on the boundary: the universal survivor of the
installed closure involution.
-/
def FixedBoundary : Set V :=
  {x : V | B.boundaryOf x ∧ B.closure.theta x = x}

/-- Membership in the fixed boundary is boundary membership plus fixedness. -/
theorem mem_fixedBoundary_iff
    (x : V) :
    x ∈ B.FixedBoundary ↔ B.boundaryOf x ∧ B.closure.theta x = x :=
  Iff.rfl

/-- A fixed-boundary point is a boundary point. -/
theorem boundaryOf_of_mem_fixedBoundary
    {x : V}
    (hx : x ∈ B.FixedBoundary) :
    B.boundaryOf x :=
  hx.1

/-- A fixed-boundary point is pointwise closure-fixed. -/
theorem theta_eq_self_of_mem_fixedBoundary
    {x : V}
    (hx : x ∈ B.FixedBoundary) :
    B.closure.theta x = x :=
  hx.2

/--
If a boundary point is fixed by closure, then it belongs to the fixed boundary.
-/
theorem mem_fixedBoundary_of_boundary_fixed
    {x : V}
    (hboundary : B.boundaryOf x)
    (hfixed : B.closure.theta x = x) :
    x ∈ B.FixedBoundary :=
  ⟨hboundary, hfixed⟩

/-- Closure acts trivially on fixed-boundary points. -/
theorem closure_of_fixedBoundary
    {x : V}
    (hx : x ∈ B.FixedBoundary) :
    B.closure.theta x = x :=
  B.theta_eq_self_of_mem_fixedBoundary hx

/--
If closure swaps two boundary points, their diagonal is fixed by the closure.

No claim is made here that the diagonal is itself on the boundary; that is
model-specific and must be supplied separately when needed.
-/
theorem swapped_boundary_diagonal_fixed
    {x y : V}
    (hx_boundary : B.boundaryOf x)
    (hy_boundary : B.boundaryOf y)
    (hxy : B.closure.theta x = y)
    (hyx : B.closure.theta y = x) :
    x + y ∈ B.closure.Fixed :=
  by
    have _hx_boundary := hx_boundary
    have _hy_boundary := hy_boundary
    exact B.closure.diagonal_fixed_of_swap hxy hyx

/--
If closure swaps two boundary points, their imbalance is anti-fixed.

The boundary hypotheses are retained to keep the theorem at the boundary layer,
although the anti-fixed algebra itself is purely linear.
-/
theorem swapped_boundary_imbalance_anti_fixed
    {x y : V}
    (hx_boundary : B.boundaryOf x)
    (hy_boundary : B.boundaryOf y)
    (hxy : B.closure.theta x = y)
    (hyx : B.closure.theta y = x) :
    B.closure.theta (x - y) = -(x - y) :=
  by
    have _hx_boundary := hx_boundary
    have _hy_boundary := hy_boundary
    exact B.closure.difference_anti_fixed_of_swap hxy hyx

end SelfDualChiralConeBoundary

/-! ## 2. Owner theorem -/

/--
Every fixed-boundary point is boundary data and is closure-fixed.
-/
theorem selfDualChiralConeBoundaryOwnerTarget :
  ∀ (V : Type*) [AddCommGroup V] [Module ℝ V],
  ∀ B : SelfDualChiralConeBoundary V,
  ∀ x : V,
    x ∈ B.FixedBoundary →
      B.boundaryOf x ∧ B.closure.theta x = x := by
  intro V _ _ B x hx
  exact hx

/-- Fixed-boundary readout for one point in a self-dual chiral cone boundary. -/
theorem fixedBoundary_packet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : SelfDualChiralConeBoundary V) {x : V}
    (hx : x ∈ B.FixedBoundary) :
    B.boundaryOf x ∧ B.closure.theta x = x :=
  selfDualChiralConeBoundaryOwnerTarget V B x hx

end InfoGeometry.OperatorAlgebra.SelfDualChiralConeBoundary
