import DAG.TypedCategory
import InfoGeometry.Meta.Architecture
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

def composableEdges : List TypedRelation → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.dst = second.src ∧ composableEdges (second :: rest)

@[simp] theorem composableEdges_nil : composableEdges [] := by
  trivial

@[simp] theorem composableEdges_single (edge : TypedRelation) :
    composableEdges [edge] := by
  trivial

theorem composableEdges_cons_cons_iff
    (first second : TypedRelation) (rest : List TypedRelation) :
    composableEdges (first :: second :: rest) ↔
      first.dst = second.src ∧ composableEdges (second :: rest) := by
  rfl

structure TypedRelationPath where
  src : Name
  dst : Name
  edges : List TypedRelation
  source_ok : edges.head?.map (·.src) = some src ∨ edges = []
  target_ok : edges.getLast?.map (·.dst) = some dst ∨ edges = []
  composable : composableEdges edges

theorem TypedRelationPath.composable_of_two
    (p : TypedRelationPath) (first second : TypedRelation)
    (hEdges : p.edges = first :: second :: []) :
    first.dst = second.src := by
  have h := p.composable
  rw [hEdges] at h
  exact h.1

def representationDistance (p : TypedRelationPath) : Option Nat :=
  if p.edges = [] then none else some p.edges.length

theorem representationDistance_some
    (p : TypedRelationPath) (h : p.edges ≠ []) :
    representationDistance p = some p.edges.length := by
  simp [representationDistance, h]

theorem representationDistance_none_iff
    (p : TypedRelationPath) :
    representationDistance p = none ↔ p.edges = [] := by
  simp [representationDistance]

theorem edges_nonempty_of_representationDistance_some
    (p : TypedRelationPath) (distance : Nat)
    (h : representationDistance p = some distance) :
    p.edges ≠ [] := by
  intro hnil
  simp [representationDistance, hnil] at h

theorem representationDistance_pos
    (p : TypedRelationPath) (h : p.edges ≠ []) :
    0 < (representationDistance p).getD 0 := by
  cases hEdges : p.edges with
  | nil => exact False.elim (h (by simp [hEdges]))
  | cons head tail => simp [representationDistance, hEdges]

def relationCone (target : Name) (relations : List TypedRelation) : Set Name :=
  {source | ∃ relation ∈ relations,
    relation.dst = target ∧ relation.src = source}

theorem mem_relationCone_iff
    (target source : Name) (relations : List TypedRelation) :
    source ∈ relationCone target relations ↔
      ∃ relation ∈ relations, relation.dst = target ∧ relation.src = source := by
  rfl

def typedSupportCone (target : Name) (relations : List TypedRelation) : Set Name :=
  {source | ∃ relation ∈ relations,
    relation.dst = target ∧ relation.src = source ∧ relation.processMorphism?.isSome}

theorem mem_typedSupportCone_iff
    (target source : Name) (relations : List TypedRelation) :
    source ∈ typedSupportCone target relations ↔
      ∃ relation ∈ relations,
        relation.dst = target ∧ relation.src = source ∧ relation.processMorphism?.isSome := by
  rfl

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
