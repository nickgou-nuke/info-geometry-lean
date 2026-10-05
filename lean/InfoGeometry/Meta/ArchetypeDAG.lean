import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Causal.ProofDAGRepresentation
import InfoGeometry.Topology.ChiralDirectedGraphHomotopy

open InfoGeometry.Causal.ProofDAGRepresentation
open InfoGeometry.Topology

namespace InfoGeometry.MetaCompiler

/-!
# Archetype Proof DAG Representation

This module bridges the epistemic archetype framework with the formal
causal DAG and homotopy categories, resolving the "Isolated Island Syndrome".

It establishes that registered `TypedArchetype`s form the vertices of a `ProofDAG`,
and that logical dependencies (or phase progressions) between archetypes form
the edges (morphisms) in the associated `ChiralPathCategory`.
-/

/-- An archetype wrapper for DAG nodes to avoid universe polymorphism issues. -/
structure ArchetypeNode where
  name : Lean.Name
  phase : Nat
  deriving DecidableEq

/-- We define a logical directed edge: a node `A` points to `B` if `A` strictly precedes `B` in phase,
or if they are the same node (for reflexivity in a partial order). -/
def ArchetypeLe (a b : ArchetypeNode) : Prop :=
  a = b ∨ a.phase < b.phase

theorem ArchetypeLe_refl (a : ArchetypeNode) : ArchetypeLe a a :=
  Or.inl rfl

theorem ArchetypeLe_trans {a b c : ArchetypeNode} (h1 : ArchetypeLe a b) (h2 : ArchetypeLe b c) : ArchetypeLe a c := by
  rcases h1 with (rfl | h1_lt)
  · exact h2
  · rcases h2 with (rfl | h2_lt)
    · exact Or.inr h1_lt
    · exact Or.inr (Nat.lt_trans h1_lt h2_lt)

theorem ArchetypeLe_antisymm {a b : ArchetypeNode} (h1 : ArchetypeLe a b) (h2 : ArchetypeLe b a) : a = b := by
  rcases h1 with (rfl | h1_lt)
  · rfl
  · rcases h2 with (rfl | h2_lt)
    · rfl
    · exact False.elim (Nat.lt_asymm h1_lt h2_lt)

/-- The Epistemic Proof DAG where archetypes are ordered by phase/logical dependency. -/
def EpistemicDAG : ProofDAG ArchetypeNode where
  le := ArchetypeLe
  refl := ArchetypeLe_refl
  trans := ArchetypeLe_trans
  antisymm := ArchetypeLe_antisymm

/-- 
Every EpistemicDAG induces a `ChiralDigraph`, allowing archetype promotion
pipelines to be formally mapped as paths (morphisms) in `ChiralPathCategory`.
-/
def EpistemicChiralDigraph : ChiralDigraph where
  Vertex := ArchetypeNode
  edge a b := a.phase < b.phase
  edge_decidable a b := inferInstance
  sector _ := ChiralSector.left -- All foundational logic is uniformly assigned to one sector here
  allowedTransition _ _ := True
  transition_decidable _ _ := inferInstance
  edge_allowed _ := trivial

end InfoGeometry.MetaCompiler
