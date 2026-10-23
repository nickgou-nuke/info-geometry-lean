/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.ChiralDirectedGraphHomotopy

/-!
# Noncommutative operator transport along directed paths

This owner closes the generic path-to-operator archetype on the existing
`DirectedPath` carrier.  An edge label takes values in an arbitrary monoid, so
the construction does not commute factors or replace operators by scalars.
The convention is left-to-right path composition: the label of a newly added
edge is multiplied on the left of the transport of the remaining path.

The owner deliberately does not identify a plabic edge label with a Clifford,
Krein, or thermodynamic operator.  Such an identification remains a separate
map with its own compatibility proof.
-/

namespace InfoGeometry.Topology

universe u v

variable {G : ChiralDigraph} {M : Type u} [Monoid M]

namespace DirectedPath

/-- Product of edge operators along a directed path. -/
def operatorTransport
    (edgeOperator : ∀ {u v : G.Vertex}, G.edge u v → M) :
    {u v : G.Vertex} → DirectedPath G u v → M
  | _, _, .refl _ => 1
  | _, _, .cons edge tail => edgeOperator edge * operatorTransport edgeOperator tail

@[simp] theorem operatorTransport_refl
    (edgeOperator : ∀ {u v : G.Vertex}, G.edge u v → M)
    (u : G.Vertex) :
    operatorTransport edgeOperator (DirectedPath.refl u) = 1 := rfl

@[simp] theorem operatorTransport_cons
    (edgeOperator : ∀ {u v : G.Vertex}, G.edge u v → M)
    {u v w : G.Vertex} (edge : G.edge u v) (tail : DirectedPath G v w) :
    operatorTransport edgeOperator (DirectedPath.cons edge tail) =
      edgeOperator edge * operatorTransport edgeOperator tail := rfl

/-- Path composition is sent to multiplication in the same order, without a
commutativity assumption on the target operator monoid. -/
theorem operatorTransport_append
    (edgeOperator : ∀ {u v : G.Vertex}, G.edge u v → M)
    {u v w : G.Vertex} (p : DirectedPath G u v) (q : DirectedPath G v w) :
    operatorTransport edgeOperator (p.append q) =
      operatorTransport edgeOperator p * operatorTransport edgeOperator q := by
  induction p with
  | refl => simp [DirectedPath.append]
  | cons edge p ih =>
      simp [DirectedPath.append, ih, mul_assoc]

end DirectedPath

namespace ChiralDigraphHom

/-- An operator label is preserved by a graph map when corresponding edges
carry equal operators. -/
theorem operatorTransport_mapPath
    {H : ChiralDigraph}
    (F : ChiralDigraphHom G H)
    (sourceOperator : ∀ {u v : G.Vertex}, G.edge u v → M)
    (targetOperator : ∀ {u v : H.Vertex}, H.edge u v → M)
    (hOperator : ∀ {u v : G.Vertex} (edge : G.edge u v),
      sourceOperator edge = targetOperator (F.mapEdge edge))
    {u v : G.Vertex} (p : DirectedPath G u v) :
    DirectedPath.operatorTransport sourceOperator p =
      DirectedPath.operatorTransport targetOperator (F.mapPath p) := by
  induction p with
  | refl => rfl
  | cons edge p ih =>
      simp only [DirectedPath.operatorTransport, ChiralDigraphHom.mapPath]
      rw [hOperator edge, ih]

end ChiralDigraphHom

end InfoGeometry.Topology
