/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import InfoGeometry.Topology.PlabicBoundaryMeasurement

/-!
# A finite planar directed network for the `Gr(2,4)` chart readout

This owner replaces the previous abstract diamond DAG by a concrete finite
directed graph together with a straight-line drawing and two source-to-sink
routes. Its finite path sum is identified with the chart's `Δ₁₃` minor.

This is not yet a Postnikov plabic graph: no trivalent internal vertices,
vertex-color data, boundary trips, or graph square move are defined here.

## i. Overview

The file defines a finite directed diamond, its planar drawing, and the two
source-to-sink path weights.

## ii. Key results

The two route weights sum to the existing `Δ₁₃` chart minor, and positive
edge weights yield a positive boundary sum.

## iii. Table of contents

* `Vertex`, `Edge`, and `directedEdge`: the finite network.
* `edgePoint` and `edge_interiors_disjoint`: a crossing-free drawing.
* `Route`, `boundaryPathSum`, and `boundaryPathSum_eq_chart_minor`: the path
  measurement and its chart comparison.

## iv. References

* `InfoGeometry.Topology.PlabicBoundaryMeasurement` for the chart minor.
* `docs/PLABIC_NETWORK_QMS_CONTRACT.md` for the bounded task contract.
-/

namespace InfoGeometry.Topology.PlanarDiamondBoundaryNetwork

open PlabicBoundaryMeasurement
open InfoGeometry.Amplituhedron

/-- Vertices of the finite two-route network: source, upper branch, lower
branch, and sink. -/
inductive Vertex
  | source
  | upper
  | lower
  | sink
  deriving DecidableEq, Repr

instance : Fintype Vertex where
  elems := {.source, .upper, .lower, .sink}
  complete := by
    intro v
    cases v <;> simp

/-- The directed edges of the diamond network, in source-to-sink order. -/
inductive Edge
  | sourceUpper
  | upperSink
  | sourceLower
  | lowerSink
  deriving DecidableEq, Repr

def edgeSource : Edge → Vertex
  | .sourceUpper => .source
  | .upperSink => .upper
  | .sourceLower => .source
  | .lowerSink => .lower

def edgeTarget : Edge → Vertex
  | .sourceUpper => .upper
  | .upperSink => .sink
  | .sourceLower => .lower
  | .lowerSink => .sink

/-- The four directed edges; no other directed transitions are present. -/
instance : Fintype Edge where
  elems := {.sourceUpper, .upperSink, .sourceLower, .lowerSink}
  complete := by
    intro e
    cases e <;> simp

def directedEdge (v w : Vertex) : Prop :=
  (v = .source ∧ w = .upper) ∨
  (v = .upper ∧ w = .sink) ∨
  (v = .source ∧ w = .lower) ∨
  (v = .lower ∧ w = .sink)

/-- Every encoded edge has the endpoint pair specified by `directedEdge`. -/
theorem edge_endpoints_are_edges (e : Edge) :
    directedEdge (edgeSource e) (edgeTarget e) := by
  cases e <;> simp [directedEdge, edgeSource, edgeTarget]

/-- Straight-line placement of the four vertices in the plane. -/
def vertexPoint : Vertex → ℝ × ℝ
  | .source => (0, 0)
  | .upper => (1, 1)
  | .lower => (1, -1)
  | .sink => (2, 0)

/-- Affine parametrization of each drawn edge for parameter `r ∈ [0,1]`. -/
def edgePoint : Edge → ℝ → ℝ × ℝ
  | .sourceUpper, r => (r, r)
  | .upperSink, r => (1 + r, 1 - r)
  | .sourceLower, r => (r, -r)
  | .lowerSink, r => (1 + r, -1 + r)

/-- The affine edge parametrization starts at its declared source vertex. -/
theorem edgePoint_start (e : Edge) : edgePoint e 0 = vertexPoint (edgeSource e) := by
  cases e <;> norm_num [edgePoint, vertexPoint, edgeSource]

/-- The affine edge parametrization ends at its declared target vertex. -/
theorem edgePoint_finish (e : Edge) : edgePoint e 1 = vertexPoint (edgeTarget e) := by
  cases e <;> norm_num [edgePoint, vertexPoint, edgeTarget]

/-- Distinct edge interiors in this straight-line drawing are disjoint. For
this four-edge graph this is the crossing-free condition: adjacent edges meet
only at their shared endpoint, while the two nonadjacent pairs do not meet. -/
theorem edge_interiors_disjoint
    (e f : Edge) (hef : e ≠ f) (s t : ℝ)
    (hs : 0 < s ∧ s < 1) (ht : 0 < t ∧ t < 1) :
    edgePoint e s ≠ edgePoint f t := by
  intro h
  cases e <;> cases f <;> simp_all [edgePoint]
    <;> rcases h with ⟨hx, hy⟩ <;> nlinarith

/-- Positive edge weights on the upper and lower routes. -/
def edgeWeight (t₁ t₂ t₃ t₄ : ℝ) : Edge → ℝ
  | .sourceUpper => t₁
  | .upperSink => t₃
  | .sourceLower => t₂
  | .lowerSink => t₄

/-- The two possible middle vertices uniquely index all directed routes from
the source to the sink in this network. -/
inductive Route
  | upper
  | lower
  deriving DecidableEq, Repr

instance : Fintype Route where
  elems := {.upper, .lower}
  complete := by
    intro p
    cases p <;> simp

def routeFirstEdge : Route → Edge
  | .upper => .sourceUpper
  | .lower => .sourceLower

def routeLastEdge : Route → Edge
  | .upper => .upperSink
  | .lower => .lowerSink

/-- The final vertex of each route's first edge is the initial vertex of its last edge. -/
theorem route_edges_compose (p : Route) :
    edgeTarget (routeFirstEdge p) = edgeSource (routeLastEdge p) := by
  cases p <;> rfl

/-- Weight of a route is the product of its two directed edge weights. -/
def routeWeight (t₁ t₂ t₃ t₄ : ℝ) (p : Route) : ℝ :=
  edgeWeight t₁ t₂ t₃ t₄ (routeFirstEdge p) *
    edgeWeight t₁ t₂ t₃ t₄ (routeLastEdge p)

/-- Finite boundary measurement from source to sink, defined as the sum over
the two directed routes. -/
def boundaryPathSum (t₁ t₂ t₃ t₄ : ℝ) : ℝ :=
  routeWeight t₁ t₂ t₃ t₄ .upper + routeWeight t₁ t₂ t₃ t₄ .lower

/-- The finite path sum expands into the products along the upper and lower routes. -/
theorem boundaryPathSum_eq_route_weights (t₁ t₂ t₃ t₄ : ℝ) :
    boundaryPathSum t₁ t₂ t₃ t₄ = t₁ * t₃ + t₂ * t₄ := by
  simp [boundaryPathSum, routeWeight, edgeWeight, routeFirstEdge,
    routeLastEdge]

/-- Positive edge weights give positive weight to each directed route. -/
theorem routeWeight_pos (t₁ t₂ t₃ t₄ : ℝ)
    (h₁ : 0 < t₁) (h₂ : 0 < t₂) (h₃ : 0 < t₃) (h₄ : 0 < t₄)
    (p : Route) : 0 < routeWeight t₁ t₂ t₃ t₄ p := by
  cases p <;> simp [routeWeight, edgeWeight, routeFirstEdge, routeLastEdge]
    <;> positivity

/-- The finite boundary readout is positive when all four edge weights are
positive. -/
theorem boundaryPathSum_pos (t₁ t₂ t₃ t₄ : ℝ)
    (h₁ : 0 < t₁) (h₂ : 0 < t₂) (h₃ : 0 < t₃) (h₄ : 0 < t₄) :
    0 < boundaryPathSum t₁ t₂ t₃ t₄ := by
  rw [boundaryPathSum_eq_route_weights]
  positivity

/-- The concrete network measurement is the `Δ₁₃` coordinate of the existing
positive matrix chart. This is a finite planar-network-to-chart comparison;
it makes no claim about plabic boundary measurement. -/
theorem boundaryPathSum_eq_chart_minor
    (t₁ t₂ t₃ t₄ : ℝ) :
    boundaryPathSum t₁ t₂ t₃ t₄ =
      minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 := by
  rw [boundaryPathSum_eq_route_weights, plucker_13]

end InfoGeometry.Topology.PlanarDiamondBoundaryNetwork
