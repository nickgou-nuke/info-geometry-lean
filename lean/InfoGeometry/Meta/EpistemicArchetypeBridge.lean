import InfoGeometry.Epistemology.JungianEpistemicCompiler
import InfoGeometry.Meta.EpistemicCompiler

namespace InfoGeometry.Meta.EpistemicArchetypeBridge

open Lean
open InfoGeometry.Epistemology.JungianEpistemicCompiler
open InfoGeometry.Meta.EpistemicCompiler

/-!
# Typed bridge for the epistemic compiler

The epistemology owner supplies the finite ordered archetypes.  The meta owner
supplies `SyntheticName` and `PosetPartiture`, which are elaboration data.
This file connects those two layers without assigning neural or psychological
semantics to Lean's metaprogramming runtime.
-/

/-- The metadata name associated with an ordered archetype. -/
def archetypeSyntheticName : UnconsciousArchetype → SyntheticName
  | .primaMateria => ⟨`Jungian.Archetype.primaMateria⟩
  | .shadowProjection => ⟨`Jungian.Archetype.shadowProjection⟩
  | .animusLogos => ⟨`Jungian.Archetype.animusLogos⟩
  | .chiralSyzygy => ⟨`Jungian.Archetype.chiralSyzygy⟩
  | .selfIndividuation => ⟨`Jungian.Archetype.selfIndividuation⟩

/-- Distinct ordered archetypes retain distinct metadata names. -/
theorem archetypeSyntheticName_injective :
    Function.Injective archetypeSyntheticName := by
  intro a b h
  cases a <;> cases b <;>
    simp [archetypeSyntheticName] at h ⊢

/-- The immediate causal predecessor represented by the five-stage chain. -/
def archetypePredecessor : UnconsciousArchetype → Option UnconsciousArchetype
  | .primaMateria => none
  | .shadowProjection => some .primaMateria
  | .animusLogos => some .shadowProjection
  | .chiralSyzygy => some .animusLogos
  | .selfIndividuation => some .chiralSyzygy

/-- Every declared predecessor is below its successor in the epistemic order. -/
theorem archetypePredecessor_le {a p : UnconsciousArchetype}
    (h : archetypePredecessor a = some p) : p ≤ a := by
  cases a <;> simp [archetypePredecessor] at h
  all_goals subst p
  all_goals decide

/-- The five ordered archetypes as metadata vertices. -/
def archetypeVertices : Array SyntheticName :=
  #[ archetypeSyntheticName .primaMateria,
     archetypeSyntheticName .shadowProjection,
     archetypeSyntheticName .animusLogos,
     archetypeSyntheticName .chiralSyzygy,
     archetypeSyntheticName .selfIndividuation ]

/-- Runtime predecessor rows for `archetypeVertices`, in chain order. -/
def archetypeEdges : Array (Array Nat) :=
  #[ #[], #[0], #[1], #[2], #[3] ]

/-- The concrete meta-level schedule for the five typed archetypes. -/
def archetypePartiture : PosetPartiture where
  vertices := archetypeVertices
  edges := archetypeEdges

/-- The bridge exposes exactly five ordered metadata vertices. -/
theorem archetypeVertices_size : archetypeVertices.size = 5 := by
  rfl

/-- The bridge exposes one predecessor row for each metadata vertex. -/
theorem archetypeEdges_size : archetypeEdges.size = archetypeVertices.size := by
  rfl

/-- The runtime partiture preserves the vertex and edge data defined above. -/
theorem archetypePartiture_data :
    archetypePartiture.vertices = archetypeVertices ∧
      archetypePartiture.edges = archetypeEdges := by
  exact ⟨rfl, rfl⟩

end InfoGeometry.Meta.EpistemicArchetypeBridge
