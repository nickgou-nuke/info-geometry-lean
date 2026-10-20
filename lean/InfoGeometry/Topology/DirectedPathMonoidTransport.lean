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

theorem DirectedPath.product_mapPath
    {G H : ChiralDigraph} (F : ChiralDigraphHom G H)
    (sourceWeight : ∀ u v : G.Vertex, G.edge u v → M)
    (targetWeight : ∀ u v : H.Vertex, H.edge u v → M)
    (hweight : ∀ {u v : G.Vertex} (e : G.edge u v),
      targetWeight (F.mapVertex u) (F.mapVertex v) (F.mapEdge e) =
        sourceWeight u v e)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    DirectedPath.product targetWeight (F.mapPath p) =
      DirectedPath.product sourceWeight p := by
  induction p with
  | refl => rfl
  | cons h p ih =>
      simp only [ChiralDigraphHom.mapPath, DirectedPath.product]
      rw [hweight h, ih]

namespace PresentedPathClass

/-- The ordered product descends to a presented path quotient when every
generating contextual rewrite preserves it. -/
def product
    (P : DirectedPathPresentation G)
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → M)
    (hcompat : ProductCompatible P edgeWeight)
    {u v : G.Vertex} : PresentedPathClass P u v → M :=
  Quot.lift (DirectedPath.product edgeWeight)
    (fun _p _q h => DirectedPath.product_eq_of_presentedHomotopy
      P edgeWeight hcompat h)

theorem product_comp
    (P : DirectedPathPresentation G)
    (edgeWeight : ∀ u v : G.Vertex, G.edge u v → M)
    (hcompat : ProductCompatible P edgeWeight)
    {u v w : G.Vertex} (p : PresentedPathClass P u v)
    (q : PresentedPathClass P v w) :
    product P edgeWeight hcompat (comp P p q) =
      product P edgeWeight hcompat p * product P edgeWeight hcompat q := by
  refine Quot.inductionOn p ?_
  intro p'
  refine Quot.inductionOn q ?_
  intro q'
  change DirectedPath.product edgeWeight (p'.append q') = _
  exact DirectedPath.product_append edgeWeight p' q'

 /-- The ordered product is preserved by a presentation-preserving graph map
    when the target edge labels pull back to the source labels. -/
theorem product_mapClass
    {G H : ChiralDigraph} (F : ChiralDigraphHom G H)
    (P : DirectedPathPresentation G) (Q : DirectedPathPresentation H)
    (hcell : ∀ {u v : G.Vertex} {p q : DirectedPath G u v},
      P.cell p q →
        Q.cell (ChiralDigraphHom.mapPath F p) (ChiralDigraphHom.mapPath F q))
    (sourceWeight : ∀ u v : G.Vertex, G.edge u v → M)
    (targetWeight : ∀ u v : H.Vertex, H.edge u v → M)
    (hweight : ∀ {u v : G.Vertex} (e : G.edge u v),
      targetWeight (F.mapVertex u) (F.mapVertex v) (F.mapEdge e) =
        sourceWeight u v e)
    (hsource : ProductCompatible P sourceWeight)
    (htarget : ProductCompatible Q targetWeight)
    {u v : G.Vertex} (p : PresentedPathClass P u v) :
    product Q targetWeight htarget (mapClass F P Q hcell p) =
      product P sourceWeight hsource p := by
  refine Quot.inductionOn p ?_
  intro p'
  change DirectedPath.product targetWeight (ChiralDigraphHom.mapPath F p') =
    DirectedPath.product sourceWeight p'
  exact DirectedPath.product_mapPath F sourceWeight targetWeight hweight p'

end PresentedPathClass

end InfoGeometry.Topology
