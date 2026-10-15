/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral directed graph paths and elementary homotopy witnesses

This is a finite/combinatorial carrier.  A directed homotopy is represented by
an explicit directed two-cell witness; no topological realization or
fundamental-group claim is made here.
-/

namespace InfoGeometry.Topology

open CategoryTheory

inductive ChiralSector
  | left | right
deriving DecidableEq, Repr

structure ChiralDigraph where
  Vertex : Type*
  edge : Vertex → Vertex → Prop
  edge_decidable : ∀ u v, Decidable (edge u v)
  sector : Vertex → ChiralSector
  allowedTransition : ChiralSector → ChiralSector → Prop
  transition_decidable : ∀ s t, Decidable (allowedTransition s t)
  edge_allowed : ∀ {u v}, edge u v → allowedTransition (sector u) (sector v)

attribute [instance] ChiralDigraph.edge_decidable
attribute [instance] ChiralDigraph.transition_decidable

inductive DirectedPath (G : ChiralDigraph) : G.Vertex → G.Vertex → Type*
  | refl (v) : DirectedPath G v v
  | cons {u v w} : G.edge u v → DirectedPath G v w → DirectedPath G u w

namespace DirectedPath

def length {G : ChiralDigraph} {u v : G.Vertex} : DirectedPath G u v → ℕ
  | .refl _ => 0
  | .cons _ p => p.length + 1

def append {G : ChiralDigraph} {u v w : G.Vertex} :
    DirectedPath G u v → DirectedPath G v w → DirectedPath G u w
  | .refl _, q => q
  | .cons h p, q => .cons h (p.append q)

@[simp] theorem length_refl {G : ChiralDigraph} (v : G.Vertex) :
    (DirectedPath.refl v).length = 0 := rfl

@[simp] theorem length_append {G : ChiralDigraph} {u v w : G.Vertex}
    (p : DirectedPath G u v) (q : DirectedPath G v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | refl => simp [append]
  | cons h p ih =>
      simp [append, length, ih, Nat.add_comm, Nat.add_assoc]

@[simp] theorem append_refl {G : ChiralDigraph} {u v : G.Vertex}
    (p : DirectedPath G u v) : p.append (.refl v) = p := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [append, ih]

theorem append_assoc {G : ChiralDigraph} {u v w z : G.Vertex}
    (p : DirectedPath G u v) (q : DirectedPath G v w) (r : DirectedPath G w z) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [append, ih]

end DirectedPath

structure DirectedChiralTwoCell (G : ChiralDigraph) (source target : G.Vertex) where
  upper : DirectedPath G source target
  lower : DirectedPath G source target
  compatible : ∀ {u v : G.Vertex}, G.edge u v →
    G.allowedTransition (G.sector u) (G.sector v)

/-- A finite directed graph with a genuine shortcut and a two-edge route. -/
def finiteTwoCellModelDigraph : ChiralDigraph where
  Vertex := Fin 3
  edge := fun u v => u < v
  edge_decidable := fun _ _ => inferInstance
  sector := fun _ => .left
  allowedTransition := fun s t => s = t
  transition_decidable := fun _ _ => inferInstance
  edge_allowed := by intro u v _; rfl

def finiteTwoCellModelDirectPath :
    DirectedPath finiteTwoCellModelDigraph (0 : Fin 3) (2 : Fin 3) :=
  .cons (by change (0 : Fin 3) < (2 : Fin 3); decide) (.refl _)

def finiteTwoCellModelCompositePath :
    DirectedPath finiteTwoCellModelDigraph (0 : Fin 3) (2 : Fin 3) :=
  .cons (by change (0 : Fin 3) < (1 : Fin 3); decide)
    (.cons (by change (1 : Fin 3) < (2 : Fin 3); decide) (.refl _))

/-- Concrete nontrivial two-cell: the direct edge and the two-edge path have
the same endpoints. -/
def finiteTwoCellModel :
    DirectedChiralTwoCell finiteTwoCellModelDigraph (0 : Fin 3) (2 : Fin 3) where
  upper := finiteTwoCellModelCompositePath
  lower := finiteTwoCellModelDirectPath
  compatible := by intro u v _; rfl

theorem finiteTwoCellModel_paths_distinct :
    finiteTwoCellModelCompositePath ≠ finiteTwoCellModelDirectPath := by
  intro h
  have hlen := congrArg
    (fun p : DirectedPath finiteTwoCellModelDigraph (0 : Fin 3) (2 : Fin 3) =>
      p.length) h
  simp [finiteTwoCellModelCompositePath, finiteTwoCellModelDirectPath,
    DirectedPath.length] at hlen

def DirectedChiralHomotopy {G : ChiralDigraph}
    {u v : G.Vertex} (p q : DirectedPath G u v) : Prop :=
  ∃ cell : DirectedChiralTwoCell G u v, cell.upper = p ∧ cell.lower = q

def DirectedChiralHomotopyRel {G : ChiralDigraph} {u v : G.Vertex} :
    DirectedPath G u v → DirectedPath G u v → Prop :=
  Relation.ReflTransGen DirectedChiralHomotopy

/-- The equivalence closure of elementary two-cell rewrites.  This is the
    undirected homotopy relation; `DirectedChiralHomotopyRel` above remains
    the directed (reflexive-transitive) relation. -/
def DirectedChiralHomotopyEquiv {G : ChiralDigraph} {u v : G.Vertex} :
    DirectedPath G u v → DirectedPath G u v → Prop :=
  Relation.EqvGen DirectedChiralHomotopy

/-! The quotient carrier is available independently of composition. -/

def DirectedPathClass (G : ChiralDigraph) (u v : G.Vertex) : Type :=
  Quot (Relation.EqvGen (@DirectedChiralHomotopy G u v))

def DirectedPathClass.mk {G : ChiralDigraph} {u v : G.Vertex}
    (p : DirectedPath G u v) : DirectedPathClass G u v :=
  Quot.mk _ p

theorem DirectedPathClass.sound {G : ChiralDigraph} {u v : G.Vertex}
    {p q : DirectedPath G u v}
    (h : DirectedChiralHomotopyEquiv p q) :
    DirectedPathClass.mk p = DirectedPathClass.mk q :=
  Quot.sound h

theorem directedChiralHomotopyRel_refl {G : ChiralDigraph}
    {u v : G.Vertex} (p : DirectedPath G u v) :
    DirectedChiralHomotopyRel p p :=
  Relation.ReflTransGen.refl

theorem directedChiralHomotopyRel_trans {G : ChiralDigraph}
    {u v : G.Vertex} {p q r : DirectedPath G u v}
    (hpq : DirectedChiralHomotopyRel p q)
    (hqr : DirectedChiralHomotopyRel q r) :
    DirectedChiralHomotopyRel p r :=
  Relation.ReflTransGen.trans hpq hqr

theorem directedChiralHomotopyEquiv_refl {G : ChiralDigraph}
    {u v : G.Vertex} (p : DirectedPath G u v) :
    DirectedChiralHomotopyEquiv p p :=
  Relation.EqvGen.refl p

theorem directedChiralHomotopyEquiv_symm {G : ChiralDigraph}
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (hpq : DirectedChiralHomotopyEquiv p q) :
    DirectedChiralHomotopyEquiv q p :=
  Relation.EqvGen.symm _ _ hpq

theorem directedChiralHomotopyEquiv_trans {G : ChiralDigraph}
    {u v : G.Vertex} {p q r : DirectedPath G u v}
    (hpq : DirectedChiralHomotopyEquiv p q)
    (hqr : DirectedChiralHomotopyEquiv q r) :
    DirectedChiralHomotopyEquiv p r :=
  Relation.EqvGen.trans _ _ _ hpq hqr

/-! A precise hypothesis for descending composition to homotopy classes. -/

def HomotopyAppendCompatible (G : ChiralDigraph) : Prop :=
  ∀ {u v w : G.Vertex} {p q : DirectedPath G u v}
    (r : DirectedPath G v w),
      DirectedChiralHomotopy p q →
        DirectedChiralHomotopyEquiv (p.append r) (q.append r)

theorem directedChiralHomotopyEquiv_append_right
    {G : ChiralDigraph} (hcompat : HomotopyAppendCompatible G)
    {u v w : G.Vertex} {p q : DirectedPath G u v}
    (r : DirectedPath G v w)
    (h : DirectedChiralHomotopyEquiv p q) :
    DirectedChiralHomotopyEquiv (p.append r) (q.append r) := by
  induction h with
  | rel p q h => exact hcompat r h
  | refl p => exact directedChiralHomotopyEquiv_refl (p.append r)
  | symm p q h ih => exact directedChiralHomotopyEquiv_symm ih
  | trans p q s h₁ h₂ ih₁ ih₂ => exact directedChiralHomotopyEquiv_trans ih₁ ih₂

def HomotopyAppendLeftCompatible (G : ChiralDigraph) : Prop :=
  ∀ {u v w : G.Vertex} (p : DirectedPath G u v)
    {q r : DirectedPath G v w},
    DirectedChiralHomotopy q r →
      DirectedChiralHomotopyEquiv (p.append q) (p.append r)

theorem directedChiralHomotopyEquiv_append_left
    {G : ChiralDigraph} (hcompat : HomotopyAppendLeftCompatible G)
    {u v w : G.Vertex} (p : DirectedPath G u v)
    {q r : DirectedPath G v w}
    (h : DirectedChiralHomotopyEquiv q r) :
    DirectedChiralHomotopyEquiv (p.append q) (p.append r) := by
  induction h with
  | rel q r h => exact hcompat p h
  | refl q => exact directedChiralHomotopyEquiv_refl (p.append q)
  | symm q r h ih => exact directedChiralHomotopyEquiv_symm ih
  | trans q r s h₁ h₂ ih₁ ih₂ => exact directedChiralHomotopyEquiv_trans ih₁ ih₂

/-! Independent local rewrites compose to a rewrite of the whole path. -/

theorem directedChiralHomotopyEquiv_append_congr
    {G : ChiralDigraph}
    (hright : HomotopyAppendCompatible G)
    (hleft : HomotopyAppendLeftCompatible G)
    {u v w : G.Vertex}
    {p p' : DirectedPath G u v} {q q' : DirectedPath G v w}
    (hpp' : DirectedChiralHomotopyEquiv p p')
    (hqq' : DirectedChiralHomotopyEquiv q q') :
    DirectedChiralHomotopyEquiv (p.append q) (p'.append q') := by
  exact directedChiralHomotopyEquiv_trans
    (directedChiralHomotopyEquiv_append_right hright q hpp')
    (directedChiralHomotopyEquiv_append_left hleft p' hqq')

/-! Composition of quotient classes is available once elementary rewrites are
compatible with appending on both sides. -/

def DirectedPathClass.comp
    {G : ChiralDigraph} (hright : HomotopyAppendCompatible G)
    (hleft : HomotopyAppendLeftCompatible G)
    {u v w : G.Vertex} :
    DirectedPathClass G u v → DirectedPathClass G v w →
      DirectedPathClass G u w := by
  intro p
  refine Quot.lift
    (fun p' => Quot.lift
      (fun q' => DirectedPathClass.mk (DirectedPath.append p' q'))
      (fun q₁ q₂ hq => Quot.sound
        (directedChiralHomotopyEquiv_append_left hleft p' hq)))
    ?_ p
  intro p₁ p₂ hp
  funext q
  refine Quot.inductionOn q ?_
  intro q'
  exact Quot.sound (directedChiralHomotopyEquiv_append_right hright q' hp)

@[simp] theorem DirectedPathClass.comp_mk_refl
    {G : ChiralDigraph} (hright : HomotopyAppendCompatible G)
    (hleft : HomotopyAppendLeftCompatible G)
    {u v : G.Vertex} (p : DirectedPathClass G u v) :
    DirectedPathClass.comp hright hleft (DirectedPathClass.mk (.refl u)) p = p := by
  refine Quot.inductionOn p ?_
  intro q
  rfl

@[simp] theorem DirectedPathClass.mk_refl_comp
    {G : ChiralDigraph} (hright : HomotopyAppendCompatible G)
    (hleft : HomotopyAppendLeftCompatible G)
    {u v : G.Vertex} (p : DirectedPathClass G u v) :
    DirectedPathClass.comp hright hleft p (DirectedPathClass.mk (.refl v)) = p := by
  refine Quot.inductionOn p ?_
  intro q
  change DirectedPathClass.mk (q.append (.refl v)) = DirectedPathClass.mk q
  rw [DirectedPath.append_refl]

theorem DirectedPathClass.comp_assoc
    {G : ChiralDigraph} (hright : HomotopyAppendCompatible G)
    (hleft : HomotopyAppendLeftCompatible G)
    {u v w z : G.Vertex}
    (p : DirectedPathClass G u v) (q : DirectedPathClass G v w)
    (r : DirectedPathClass G w z) :
    DirectedPathClass.comp hright hleft
        (DirectedPathClass.comp hright hleft p q) r =
      DirectedPathClass.comp hright hleft p
        (DirectedPathClass.comp hright hleft q r) := by
  refine Quot.inductionOn p ?_
  intro p'
  refine Quot.inductionOn q ?_
  intro q'
  refine Quot.inductionOn r ?_
  intro r'
  change DirectedPathClass.mk ((p'.append q').append r') =
    DirectedPathClass.mk (p'.append (q'.append r'))
  rw [DirectedPath.append_assoc]

/-! The quotient paths form a category once append compatibility is supplied. -/

def ChiralPathQuotientCategory (G : ChiralDigraph) : Type := G.Vertex

namespace ChiralPathQuotientCategory

def category (G : ChiralDigraph)
    (hright : HomotopyAppendCompatible G)
    (hleft : HomotopyAppendLeftCompatible G) :
    Category (ChiralPathQuotientCategory G) where
  Hom u v := DirectedPathClass G u v
  id u := DirectedPathClass.mk (.refl u)
  comp p q := DirectedPathClass.comp hright hleft p q
  id_comp := by
    intro X Y f
    exact DirectedPathClass.comp_mk_refl hright hleft f
  comp_id := by
    intro X Y f
    exact DirectedPathClass.mk_refl_comp hright hleft f
  assoc := by
    intro W X Y Z f g h
    exact DirectedPathClass.comp_assoc hright hleft f g h

end ChiralPathQuotientCategory

theorem DirectedChiralHomotopy.length_eq {G : ChiralDigraph}
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (h : DirectedChiralHomotopy p q)
    (hlen : ∀ cell : DirectedChiralTwoCell G u v,
      cell.upper = p → cell.lower = q → cell.upper.length = cell.lower.length) :
    p.length = q.length := by
  rcases h with ⟨cell, hu, hl⟩
  rw [← hu, ← hl]
  exact hlen cell hu hl

/-! ### A finite edge-cost interface

This is deliberately a parameterized observable: no metric, probability
model, or geometric realization is assumed. -/

structure ChiralEdgeCost (G : ChiralDigraph) where
  cost : ∀ {u v : G.Vertex}, G.edge u v → ℝ
  nonneg : ∀ {u v : G.Vertex} (e : G.edge u v), 0 ≤ cost e

def DirectedPath.energy {G : ChiralDigraph} (C : ChiralEdgeCost G)
    {u v : G.Vertex} : DirectedPath G u v → ℝ
  | .refl _ => 0
  | .cons e p => C.cost e + p.energy C

@[simp] theorem DirectedPath.energy_refl {G : ChiralDigraph}
    (C : ChiralEdgeCost G) (u : G.Vertex) :
    (DirectedPath.refl u).energy C = 0 := rfl

theorem DirectedPath.energy_nonneg {G : ChiralDigraph}
    (C : ChiralEdgeCost G) {u v : G.Vertex} (p : DirectedPath G u v) :
    0 ≤ p.energy C := by
  induction p with
  | refl => exact le_rfl
  | cons e p ih => exact add_nonneg (C.nonneg e) ih

theorem DirectedPath.energy_append {G : ChiralDigraph}
    (C : ChiralEdgeCost G) {u v w : G.Vertex}
    (p : DirectedPath G u v) (q : DirectedPath G v w) :
    (p.append q).energy C = p.energy C + q.energy C := by
  induction p with
  | refl => simp [DirectedPath.append, DirectedPath.energy]
  | cons e p ih => simp [DirectedPath.append, DirectedPath.energy, ih, add_assoc]

theorem energy_preserved_under_chiral_cell
    {G : ChiralDigraph} (C : ChiralEdgeCost G)
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (h : DirectedChiralHomotopy p q)
    (heq : ∀ cell : DirectedChiralTwoCell G u v,
      cell.upper = p → cell.lower = q →
        cell.upper.energy C = cell.lower.energy C) :
    p.energy C = q.energy C := by
  rcases h with ⟨cell, hu, hl⟩
  rw [← hu, ← hl]
  exact heq cell hu hl

theorem DirectedPath.energy_preserved_under_homotopy_equiv
    {G : ChiralDigraph} (C : ChiralEdgeCost G)
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (hcell : ∀ {a b : G.Vertex} {r s : DirectedPath G a b},
      DirectedChiralHomotopy r s → r.energy C = s.energy C)
    (h : DirectedChiralHomotopyEquiv p q) :
    p.energy C = q.energy C := by
  induction h with
  | rel p q h => exact hcell h
  | refl p => rfl
  | symm p q h ih => exact ih.symm
  | trans p q r h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

structure ChiralDigraphHom (G H : ChiralDigraph) where
  mapVertex : G.Vertex → H.Vertex
  mapEdge : ∀ {u v}, G.edge u v → H.edge (mapVertex u) (mapVertex v)
  mapTransition : ∀ {u v}, G.edge u v →
    H.allowedTransition (H.sector (mapVertex u)) (H.sector (mapVertex v))

namespace ChiralDigraphHom

def id (G : ChiralDigraph) : ChiralDigraphHom G G where
  mapVertex := _root_.id
  mapEdge h := h
  mapTransition h := G.edge_allowed h

def comp {G H K : ChiralDigraph}
    (F : ChiralDigraphHom G H) (E : ChiralDigraphHom H K) :
    ChiralDigraphHom G K where
  mapVertex := E.mapVertex ∘ F.mapVertex
  mapEdge h := E.mapEdge (F.mapEdge h)
  mapTransition h := E.mapTransition (F.mapEdge h)

def mapPath {G H : ChiralDigraph} (F : ChiralDigraphHom G H)
    {u v : G.Vertex} : DirectedPath G u v →
      DirectedPath H (F.mapVertex u) (F.mapVertex v)
  | .refl u => .refl (F.mapVertex u)
  | .cons h p => .cons (F.mapEdge h) (F.mapPath p)

@[simp] theorem mapPath_length {G H : ChiralDigraph} (F : ChiralDigraphHom G H)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    (F.mapPath p).length = p.length := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [mapPath, DirectedPath.length, ih]

@[simp] theorem mapPath_append {G H : ChiralDigraph} (F : ChiralDigraphHom G H)
    {u v w : G.Vertex} (p : DirectedPath G u v) (q : DirectedPath G v w) :
    F.mapPath (p.append q) = (F.mapPath p).append (F.mapPath q) := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [mapPath, DirectedPath.append, ih]

@[simp] theorem mapPath_id {G : ChiralDigraph} {u v : G.Vertex}
    (p : DirectedPath G u v) : (id G).mapPath p = p := by
  induction p with
  | refl => rfl
  | cons h p ih =>
      change DirectedPath.cons h ((id G).mapPath p) = DirectedPath.cons h p
      rw [ih]
      rfl

@[simp] theorem mapPath_comp {G H K : ChiralDigraph}
    (F : ChiralDigraphHom G H) (E : ChiralDigraphHom H K)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    (comp F E).mapPath p = E.mapPath (F.mapPath p) := by
  induction p with
  | refl => rfl
  | cons h p ih =>
      change DirectedPath.cons (E.mapEdge (F.mapEdge h)) ((comp F E).mapPath p) =
        DirectedPath.cons (E.mapEdge (F.mapEdge h)) (E.mapPath (F.mapPath p))
      rw [ih]
      rfl

end ChiralDigraphHom

structure ChiralDigraphCostHom (G H : ChiralDigraph) where
  hom : ChiralDigraphHom G H
  sourceCost : ChiralEdgeCost G
  targetCost : ChiralEdgeCost H
  edge_cost_preserved : ∀ {u v : G.Vertex} (e : G.edge u v),
    sourceCost.cost e = targetCost.cost (hom.mapEdge e)

/-- Positive unit cost on every edge of the finite two-cell model graph. -/
def finiteTwoCellModelEdgeCost : ChiralEdgeCost finiteTwoCellModelDigraph where
  cost := fun _ => 1
  nonneg := by intro u v e; norm_num

/-- The identity map preserves this genuinely positive edge cost. -/
def finiteTwoCellModelCostHom :
    ChiralDigraphCostHom finiteTwoCellModelDigraph finiteTwoCellModelDigraph where
  hom := ChiralDigraphHom.id finiteTwoCellModelDigraph
  sourceCost := finiteTwoCellModelEdgeCost
  targetCost := finiteTwoCellModelEdgeCost
  edge_cost_preserved := by
    intro u v e
    simp [finiteTwoCellModelEdgeCost, ChiralDigraphHom.id]

theorem finiteTwoCellModelCostHom_positive_edge :
    finiteTwoCellModelEdgeCost.cost (by
      change (0 : Fin 3) < (1 : Fin 3)
      norm_num) = 1 := rfl

theorem ChiralDigraphCostHom.mapPath_energy
    {G H : ChiralDigraph} (F : ChiralDigraphCostHom G H)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    (F.hom.mapPath p).energy F.targetCost = p.energy F.sourceCost := by
  induction p with
  | refl => rfl
  | cons e p ih =>
    simp [ChiralDigraphHom.mapPath, DirectedPath.energy, ih,
      F.edge_cost_preserved e]

structure ChiralDigraphHomWithCells (G H : ChiralDigraph)
    extends ChiralDigraphHom G H where
  mapCell : ∀ {u v : G.Vertex}, DirectedChiralTwoCell G u v →
    DirectedChiralTwoCell H (mapVertex u) (mapVertex v)
  mapCell_upper : ∀ {u v : G.Vertex} (cell : DirectedChiralTwoCell G u v),
    (mapCell cell).upper =
      ChiralDigraphHom.mapPath toChiralDigraphHom cell.upper
  mapCell_lower : ∀ {u v : G.Vertex} (cell : DirectedChiralTwoCell G u v),
    (mapCell cell).lower =
      ChiralDigraphHom.mapPath toChiralDigraphHom cell.lower

/-- Identity map with the concrete two-cell structure preserved. -/
def finiteTwoCellModelHomWithCells :
    ChiralDigraphHomWithCells finiteTwoCellModelDigraph finiteTwoCellModelDigraph where
  toChiralDigraphHom := ChiralDigraphHom.id finiteTwoCellModelDigraph
  mapCell := fun cell => cell
  mapCell_upper := by
    intro u v cell
    exact (ChiralDigraphHom.mapPath_id cell.upper).symm
  mapCell_lower := by
    intro u v cell
    exact (ChiralDigraphHom.mapPath_id cell.lower).symm

namespace ChiralDigraphHomWithCells

def mapElementary {G H : ChiralDigraph} (F : ChiralDigraphHomWithCells G H)
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (h : DirectedChiralHomotopy p q) :
    DirectedChiralHomotopy (ChiralDigraphHom.mapPath F.toChiralDigraphHom p)
      (ChiralDigraphHom.mapPath F.toChiralDigraphHom q) := by
  rcases h with ⟨cell, hu, hl⟩
  refine ⟨F.mapCell cell, ?_, ?_⟩
  · exact (F.mapCell_upper cell).trans
      (congrArg (ChiralDigraphHom.mapPath F.toChiralDigraphHom) hu)
  · exact (F.mapCell_lower cell).trans
      (congrArg (ChiralDigraphHom.mapPath F.toChiralDigraphHom) hl)

theorem mapEquiv {G H : ChiralDigraph} (F : ChiralDigraphHomWithCells G H)
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (h : DirectedChiralHomotopyEquiv p q) :
    DirectedChiralHomotopyEquiv (ChiralDigraphHom.mapPath F.toChiralDigraphHom p)
      (ChiralDigraphHom.mapPath F.toChiralDigraphHom q) := by
  induction h with
  | rel p q h => exact Relation.EqvGen.rel _ _ (F.mapElementary h)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q h ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def mapClass {G H : ChiralDigraph} (F : ChiralDigraphHomWithCells G H)
    {u v : G.Vertex} : DirectedPathClass G u v →
      DirectedPathClass H (F.mapVertex u) (F.mapVertex v) :=
  Quot.lift
    (fun p => DirectedPathClass.mk (ChiralDigraphHom.mapPath F.toChiralDigraphHom p))
    (fun _ _ h => Quot.sound (F.mapEquiv h))

@[simp] theorem mapClass_mk {G H : ChiralDigraph}
    (F : ChiralDigraphHomWithCells G H)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    F.mapClass (DirectedPathClass.mk p) =
      DirectedPathClass.mk (ChiralDigraphHom.mapPath F.toChiralDigraphHom p) := rfl

end ChiralDigraphHomWithCells

/-! ### The raw directed path category

The quotient by homotopy is intentionally not installed here: doing so
requires a congruence theorem for `append`.  The raw paths already form a
small category, and provide the correct carrier for that later quotient. -/

def ChiralPathCategory (G : ChiralDigraph) : Type := G.Vertex

namespace ChiralPathCategory

instance (G : ChiralDigraph) : Category (ChiralPathCategory G) where
  Hom u v := DirectedPath G u v
  id u := DirectedPath.refl u
  comp p q := DirectedPath.append p q
  id_comp := by
    intro X Y f
    cases f <;> rfl
  comp_id := by
    intro X Y f
    exact DirectedPath.append_refl f
  assoc := by
    intro W X Y Z f g h
    exact DirectedPath.append_assoc f g h

end ChiralPathCategory

/-! ### Presented directed two-complexes

The legacy `DirectedChiralTwoCell` above is only a record of two parallel
paths; its transition field is automatic from `ChiralDigraph.edge_allowed`.
It must not be used as evidence that a particular pair of paths is homotopic.
The presentation below instead carries an explicit relation of generating
two-cells. Homotopy is generated only by those declared cells and their
left/right path contexts.
-/

/-- A presentation of elementary two-cells for a directed graph. The cell
relation is explicit input; an empty relation gives the free path category. -/
structure DirectedPathPresentation (G : ChiralDigraph) where
  cell : ∀ {u v : G.Vertex}, DirectedPath G u v → DirectedPath G u v → Prop

/-- The empty presentation adds no path equations. -/
def emptyPathPresentation (G : ChiralDigraph) : DirectedPathPresentation G where
  cell := fun _ _ => False

/-- One generating path rewrite, closed under composing it with paths on either
side. This is the contextual closure of the cells in a presentation. -/
inductive ContextualPathRewrite {G : ChiralDigraph}
    (P : DirectedPathPresentation G) :
    {u v : G.Vertex} → DirectedPath G u v → DirectedPath G u v → Prop
  | generator {u v : G.Vertex} {p q : DirectedPath G u v} :
      P.cell p q → ContextualPathRewrite P p q
  | appendRight {u v w : G.Vertex} {p q : DirectedPath G u v}
      (h : ContextualPathRewrite P p q) (r : DirectedPath G v w) :
      ContextualPathRewrite P (p.append r) (q.append r)
  | appendLeft {u v w : G.Vertex} (p : DirectedPath G u v)
      {q r : DirectedPath G v w} (h : ContextualPathRewrite P q r) :
      ContextualPathRewrite P (p.append q) (p.append r)

/-- Equivalence generated by the presented contextual path rewrites. -/
def PresentedPathHomotopy {G : ChiralDigraph} (P : DirectedPathPresentation G)
    {u v : G.Vertex} (p q : DirectedPath G u v) : Prop :=
  Relation.EqvGen (ContextualPathRewrite P) p q

/-- In the empty presentation, generated path homotopy is just equality of
paths. This makes explicit that the free path category retains distinct
parallel paths. -/
theorem emptyContextualPathRewrite_eq {G : ChiralDigraph}
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (h : ContextualPathRewrite (emptyPathPresentation G) p q) : p = q := by
  induction h with
  | generator cell => cases cell
  | appendRight _ r ih => exact congrArg (fun path => path.append r) ih
  | appendLeft p _ ih => exact congrArg (fun path => p.append path) ih

theorem emptyPresentedPathHomotopy_iff {G : ChiralDigraph}
    {u v : G.Vertex} {p q : DirectedPath G u v} :
    PresentedPathHomotopy (emptyPathPresentation G) p q ↔ p = q := by
  constructor
  · intro h
    induction h with
    | rel p q step => exact emptyContextualPathRewrite_eq step
    | refl p => rfl
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- A one-step contextual rewrite remains a one-step rewrite after appending
on the right. -/
theorem ContextualPathRewrite.append_right_of
    {G : ChiralDigraph} {P : DirectedPathPresentation G}
    {u v : G.Vertex} {p q : DirectedPath G u v}
    (h : ContextualPathRewrite P p q) {w : G.Vertex}
    (r : DirectedPath G v w) :
    ContextualPathRewrite P (p.append r) (q.append r) :=
  .appendRight h r

/-- Presented homotopy is stable under appending a path on the right. -/
theorem PresentedPathHomotopy.append_right
    {G : ChiralDigraph} (P : DirectedPathPresentation G)
    {u v w : G.Vertex} {p q : DirectedPath G u v}
    (h : PresentedPathHomotopy P p q) (r : DirectedPath G v w) :
    PresentedPathHomotopy P (p.append r) (q.append r) := by
  induction h with
  | rel p q h => exact Relation.EqvGen.rel _ _ (.appendRight h r)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q h ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q s h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Presented homotopy is stable under appending a path on the left. -/
theorem PresentedPathHomotopy.append_left
    {G : ChiralDigraph} (P : DirectedPathPresentation G)
    {u v w : G.Vertex} (p : DirectedPath G u v)
    {q r : DirectedPath G v w}
    (h : PresentedPathHomotopy P q r) :
    PresentedPathHomotopy P (p.append q) (p.append r) := by
  induction h with
  | rel q r h => exact Relation.EqvGen.rel _ _ (.appendLeft p h)
  | refl q => exact Relation.EqvGen.refl _
  | symm q r h ih => exact Relation.EqvGen.symm _ _ ih
  | trans q r s h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Homotopy is compatible with simultaneous replacement of both factors in a
composite path. -/
theorem PresentedPathHomotopy.append_congr
    {G : ChiralDigraph} (P : DirectedPathPresentation G)
    {u v w : G.Vertex} {p p' : DirectedPath G u v}
    {q q' : DirectedPath G v w}
    (hp : PresentedPathHomotopy P p p')
    (hq : PresentedPathHomotopy P q q') :
    PresentedPathHomotopy P (p.append q) (p'.append q') := by
  exact Relation.EqvGen.trans _ _ _
    (PresentedPathHomotopy.append_right P hp q)
    (PresentedPathHomotopy.append_left P p' hq)

/-- Quotient of paths by an explicitly presented two-cell relation. -/
abbrev PresentedPathClass {G : ChiralDigraph} (P : DirectedPathPresentation G)
    (u v : G.Vertex) : Type :=
  Quot (fun p q : DirectedPath G u v => PresentedPathHomotopy P p q)

namespace PresentedPathClass

def mk {G : ChiralDigraph} {P : DirectedPathPresentation G}
    {u v : G.Vertex} (p : DirectedPath G u v) : PresentedPathClass P u v :=
  Quot.mk (fun p q : DirectedPath G u v => PresentedPathHomotopy P p q) p

/-- Distinct parallel paths remain distinct morphisms in the free category
obtained from the empty presentation. -/
theorem emptyPresentedPathClass_ne {G : ChiralDigraph}
    {u v : G.Vertex} {p q : DirectedPath G u v} (hne : p ≠ q) :
    mk (P := emptyPathPresentation G) p ≠ mk q := by
  intro h
  have hrel := Quot.eqvGen_exact h
  have hHomEquiv : _root_.Equivalence (fun (a b : DirectedPath G u v) =>
      PresentedPathHomotopy (emptyPathPresentation G) a b) := by
    simpa [PresentedPathHomotopy] using
      (Relation.EqvGen.is_equivalence
        (ContextualPathRewrite (emptyPathPresentation G)))
  have hhom := (_root_.Equivalence.eqvGen_iff hHomEquiv).mp hrel
  exact hne (emptyPresentedPathHomotopy_iff.mp hhom)

def comp {G : ChiralDigraph} (P : DirectedPathPresentation G)
    {u v w : G.Vertex} : PresentedPathClass P u v → PresentedPathClass P v w →
      PresentedPathClass P u w := by
  intro p
  refine Quot.lift
    (fun p' => Quot.lift (fun q' => mk (p'.append q'))
      (fun q₁ q₂ hq => Quot.sound (PresentedPathHomotopy.append_left P p' hq)))
    ?_ p
  intro p₁ p₂ hp
  funext q
  refine Quot.inductionOn q ?_
  intro q'
  exact Quot.sound (PresentedPathHomotopy.append_right P hp q')

@[simp] theorem comp_mk_refl {G : ChiralDigraph}
    (P : DirectedPathPresentation G) {u v : G.Vertex}
    (p : PresentedPathClass P u v) :
    comp P (mk (DirectedPath.refl u)) p = p := by
  refine Quot.inductionOn p ?_
  intro q
  rfl

@[simp] theorem mk_refl_comp {G : ChiralDigraph}
    (P : DirectedPathPresentation G) {u v : G.Vertex}
    (p : PresentedPathClass P u v) :
    comp P p (mk (DirectedPath.refl v)) = p := by
  refine Quot.inductionOn p ?_
  intro q
  change mk (q.append (DirectedPath.refl v)) = mk q
  rw [DirectedPath.append_refl]

theorem comp_assoc {G : ChiralDigraph}
    (P : DirectedPathPresentation G) {u v w z : G.Vertex}
    (p : PresentedPathClass P u v) (q : PresentedPathClass P v w)
    (r : PresentedPathClass P w z) :
    comp P (comp P p q) r = comp P p (comp P q r) := by
  refine Quot.inductionOn p ?_
  intro p'
  refine Quot.inductionOn q ?_
  intro q'
  refine Quot.inductionOn r ?_
  intro r'
  change mk ((p'.append q').append r') = mk (p'.append (q'.append r'))
  rw [DirectedPath.append_assoc]

end PresentedPathClass

/-- Category of paths modulo the declared contextual two-cell presentation. -/
def PresentedPathCategory {G : ChiralDigraph}
    (P : DirectedPathPresentation G) : Type := G.Vertex

namespace PresentedPathCategory

instance {G : ChiralDigraph} (P : DirectedPathPresentation G) :
    Category (PresentedPathCategory P) where
  Hom u v := PresentedPathClass P u v
  id u := PresentedPathClass.mk (DirectedPath.refl u)
  comp p q := PresentedPathClass.comp P p q
  id_comp := by
    intro X Y f
    exact PresentedPathClass.comp_mk_refl P f
  comp_id := by
    intro X Y f
    exact PresentedPathClass.mk_refl_comp P f
  assoc := by
    intro W X Y Z f g h
    exact PresentedPathClass.comp_assoc P f g h

end PresentedPathCategory

end InfoGeometry.Topology
