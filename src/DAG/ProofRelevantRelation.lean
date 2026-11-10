import DAG.TypedCategory
import InfoGeometry.Meta.Architecture
import Mathlib.Data.List.Chain
import Mathlib.Data.Set.Defs

/-!
# Typed mathematical relation paths

Finite, executable relation data with no deferred proof or witness fields.
-/

namespace DAG

open Lean

inductive RelationKind
  | definitionalEquality
  | propositionalEquality
  | equivalence
  | embedding
  | quotient
  | hom
  | representation
  | transport
  | readout
  | invariantAgreement
  | compatibility
  | obstruction
  deriving Repr, BEq

structure TypedRelation where
  src : Name
  dst : Name
  relationKind : RelationKind
  processMorphism? : Option TypedDeclMorphism := none
  srcDepth? : Option RepDepth := none
  dstDepth? : Option RepDepth := none

structure TypedRelationPath where
  src : Name
  dst : Name
  edges : List TypedRelation
  endpoints :
    (edges.head?.map (·.src) = some src ∧ edges.getLast?.map (·.dst) = some dst) ∨
    (edges = [] ∧ src = dst)
  composable : List.IsChain (fun first second => first.dst = second.src) edges

theorem TypedRelationPath.endpoints_of_nonempty
    (p : TypedRelationPath) (hEdges : p.edges ≠ []) :
    p.edges.head?.map (·.src) = some p.src ∧
      p.edges.getLast?.map (·.dst) = some p.dst := by
  rcases p.endpoints with hEndpoints | ⟨hEmpty, _⟩
  · exact hEndpoints
  · exact False.elim (hEdges hEmpty)

/-- Every decomposition of a composable path containing adjacent edges exposes
the corresponding endpoint match. This applies at any position and for any
path length. -/
theorem TypedRelationPath.edge_match_of_adjacent_decomposition
    (p : TypedRelationPath) (before after : List TypedRelation)
    (first second : TypedRelation)
    (hEdges : p.edges = before ++ first :: second :: after) :
    first.dst = second.src := by
  exact List.isChain_iff_forall_rel_of_append_cons_cons.mp p.composable hEdges

def representationDistance (p : TypedRelationPath) : Nat := p.edges.length

theorem representationDistance_pos_iff_edges_nonempty
    (p : TypedRelationPath) :
    0 < representationDistance p ↔ p.edges ≠ [] := by
  cases hEdges : p.edges with
  | nil => simp [representationDistance, hEdges]
  | cons head tail => simp [representationDistance, hEdges]

def relationCone (target : Name) (relations : List TypedRelation) : Set Name :=
  {source | ∃ relation ∈ relations,
    relation.dst = target ∧ relation.src = source}

def typedSupportCone (target : Name) (relations : List TypedRelation) : Set Name :=
  {source | ∃ relation ∈ relations,
    relation.dst = target ∧ relation.src = source ∧ relation.processMorphism?.isSome}

theorem typedSupportCone_subset_relationCone
    (target : Name) (relations : List TypedRelation) :
    typedSupportCone target relations ⊆ relationCone target relations := by
  intro source hsource
  rcases hsource with ⟨relation, hrel, hdst, hsrc, _⟩
  exact ⟨relation, hrel, hdst, hsrc⟩

theorem relationCone_mono
    (target : Name) {relations₁ relations₂ : List TypedRelation}
    (h : ∀ relation, relation ∈ relations₁ → relation ∈ relations₂) :
    relationCone target relations₁ ⊆ relationCone target relations₂ := by
  intro source hsource
  rcases hsource with ⟨relation, hrel, hdst, hsrc⟩
  exact ⟨relation, h relation hrel, hdst, hsrc⟩

theorem typedSupportCone_mono
    (target : Name) {relations₁ relations₂ : List TypedRelation}
    (h : ∀ relation, relation ∈ relations₁ → relation ∈ relations₂) :
    typedSupportCone target relations₁ ⊆ typedSupportCone target relations₂ := by
  intro source hsource
  rcases hsource with ⟨relation, hrel, hdst, hsrc, hprocess⟩
  exact ⟨relation, h relation hrel, hdst, hsrc, hprocess⟩

theorem relationCone_append
    (target : Name) (relations₁ relations₂ : List TypedRelation) :
    relationCone target (relations₁ ++ relations₂) =
      relationCone target relations₁ ∪ relationCone target relations₂ := by
  apply Set.ext
  intro source
  constructor
  · rintro ⟨relation, hrel, hdst, hsrc⟩
    simp only [List.mem_append] at hrel
    rcases hrel with hrel | hrel
    · exact Or.inl ⟨relation, hrel, hdst, hsrc⟩
    · exact Or.inr ⟨relation, hrel, hdst, hsrc⟩
  · intro hsource
    rcases hsource with hsource | hsource
    · rcases hsource with ⟨relation, hrel, hdst, hsrc⟩
      exact ⟨relation, List.mem_append_left _ hrel, hdst, hsrc⟩
    · rcases hsource with ⟨relation, hrel, hdst, hsrc⟩
      exact ⟨relation, List.mem_append_right _ hrel, hdst, hsrc⟩

theorem typedSupportCone_append
    (target : Name) (relations₁ relations₂ : List TypedRelation) :
    typedSupportCone target (relations₁ ++ relations₂) =
      typedSupportCone target relations₁ ∪ typedSupportCone target relations₂ := by
  apply Set.ext
  intro source
  constructor
  · rintro ⟨relation, hrel, hdst, hsrc, hprocess⟩
    simp only [List.mem_append] at hrel
    rcases hrel with hrel | hrel
    · exact Or.inl ⟨relation, hrel, hdst, hsrc, hprocess⟩
    · exact Or.inr ⟨relation, hrel, hdst, hsrc, hprocess⟩
  · intro hsource
    rcases hsource with hsource | hsource
    · rcases hsource with ⟨relation, hrel, hdst, hsrc, hprocess⟩
      exact ⟨relation, List.mem_append_left _ hrel, hdst, hsrc, hprocess⟩
    · rcases hsource with ⟨relation, hrel, hdst, hsrc, hprocess⟩
      exact ⟨relation, List.mem_append_right _ hrel, hdst, hsrc, hprocess⟩

end DAG
