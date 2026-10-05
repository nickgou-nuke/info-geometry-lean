import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Data.Nat.Prime.Basic

open InfoGeometry.MetaCompiler

def primeCandidateArch : TypedArchetype Nat .candidate where
  name     := `primeCandidateArch
  phase    := 1
  claim    := fun n => n > 1 → ∃ p, Nat.Prime p ∧ p ∣ n
  evidence := trivial

#register_archetype primeCandidateArch
#audit_archetype primeCandidateArch
#search_typed_archetypes
