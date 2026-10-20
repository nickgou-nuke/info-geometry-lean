/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Group.Basic
import InfoGeometry.Topology.ChiralDirectedGraphHomotopy

/-!
# Multiplicative transport along directed paths

An edge-labelled path has a canonical ordered product in any monoid.  The
construction is independent of a particular graph realization and descends
through a presented path relation exactly when every generating rewrite
preserves the product.
-/

namespace InfoGeometry.Topology

variable {G : ChiralDigraph} {M : Type*} [Monoid M]

/-- Ordered product of the labels along a directed path. -/
def DirectedPath.product (edgeWeight : ∀ u v : G.Vertex, G.edge u v → M)
    {u v : G.Vertex} : DirectedPath G u v → M
  | .refl _ => 1
  | .cons h p =>
      edgeWeight _ _ h * DirectedPath.product edgeWeight p

theorem DirectedPath.product_append
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → M)
    {u v w : G.Vertex} (p : DirectedPath G u v) (q : DirectedPath G v w) :
    DirectedPath.product edgeWeight (p.append q) =
      DirectedPath.product edgeWeight p * DirectedPath.product edgeWeight q := by
  induction p with
  | refl => simp [DirectedPath.append, DirectedPath.product]
  | cons h p ih =>
      simp [DirectedPath.append, DirectedPath.product, ih, mul_assoc]

/-- A presented rewrite system is product-compatible when each contextual
rewrite preserves the ordered edge product. -/
def ProductCompatible (P : DirectedPathPresentation G)
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → M) : Prop :=
  ∀ {u v : G.Vertex} {p q : DirectedPath G u v},
    ContextualPathRewrite P p q →
      DirectedPath.product edgeWeight p = DirectedPath.product edgeWeight q

theorem DirectedPath.product_eq_of_presentedHomotopy
    (P : DirectedPathPresentation G)
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → M)
    (hcompat : ProductCompatible P edgeWeight)
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (h : PresentedPathHomotopy P p q) :
    DirectedPath.product edgeWeight p = DirectedPath.product edgeWeight q := by
  induction h with
  | rel p q hstep => exact hcompat hstep
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end InfoGeometry.Topology
