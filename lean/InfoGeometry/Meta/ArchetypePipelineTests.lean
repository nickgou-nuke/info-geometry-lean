import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Data.Nat.Prime.Basic

open InfoGeometry.MetaCompiler

/-- Every integer `n > 1` admits a prime divisor.  This is a genuine
kernel-checked closure of the archetype claim: the `.proved` evidence field
carries Mathlib's `Nat.exists_prime_and_dvd`; candidate stages carry only the
`PUnit` marker and cannot be used to extract claim proofs. -/
def primeCandidateArch : TypedArchetype Nat .proved where
  name     := `primeCandidateArch
  phase    := 1
  claim    := fun n => n > 1 → ∃ p, Nat.Prime p ∧ p ∣ n
  evidence := fun n _ => Nat.exists_prime_and_dvd (by omega)

#register_archetype primeCandidateArch
#audit_archetype primeCandidateArch
#search_typed_archetypes
