import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Data.Nat.Prime.Basic

open InfoGeometry.MetaCompiler

/-- Every integer `n > 1` admits a prime divisor.  This is a genuine
kernel-checked closure of the archetype claim: the `evidence` field now
carries Mathlib's `Nat.exists_prime_and_dvd` rather than the vacuous
`trivial : True` that a `.candidate` stage requires. -/
def primeCandidateArch : TypedArchetype Nat .proved where
  name     := `primeCandidateArch
  phase    := 1
  claim    := fun n => n > 1 → ∃ p, Nat.Prime p ∧ p ∣ n
  evidence := fun n _ => Nat.exists_prime_and_dvd (by omega)

#register_archetype primeCandidateArch
#audit_archetype primeCandidateArch
#search_typed_archetypes
