import Mathlib

/-!
# Concrete `B₃ → S₃` Artin quotient shadow

The old version of this file only exposed the type of a possible homomorphism.
This file proves the concrete finite permutation shadow: the two adjacent
transpositions `(0 1)` and `(1 2)` in `S₃` satisfy the `B₃` Artin relation.

This is still a finite quotient shadow, not a proof that an arbitrary abstract
`B₃` presentation has been quotiented by all braid relations.  It is the concrete
kernel-checked generator relation needed by later finite S3 quotient bridges.
-/

namespace InfoGeometry.Topology.ArtinBraidS3Quotient

/-- The two adjacent Artin generators of `B₃`. -/
abbrev B3Gen := Fin 2

/-- The permutation shadow of `σ₁`. -/
def sigma1 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The permutation shadow of `σ₂`. -/
def sigma2 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Map adjacent `B₃` generator labels to the adjacent transpositions in `S₃`. -/
def s3ArtinGenerator : B3Gen → Equiv.Perm (Fin 3)
  | ⟨0, _⟩ => sigma1
  | ⟨1, _⟩ => sigma2

/-- The first generator is the transposition `(0 1)`. -/
theorem s3ArtinGenerator_zero :
    s3ArtinGenerator ⟨0, by decide⟩ = sigma1 := by
  rfl

/-- The second generator is the transposition `(1 2)`. -/
theorem s3ArtinGenerator_one :
    s3ArtinGenerator ⟨1, by decide⟩ = sigma2 := by
  rfl

/-- Adjacent transpositions in `S₃` satisfy the `B₃` Artin braid relation. -/
theorem s3_adjacent_artin_relation :
    sigma1 * sigma2 * sigma1 = sigma2 * sigma1 * sigma2 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

/-- The first adjacent transposition squares to the identity in the `S₃` quotient. -/
theorem sigma1_sq :
    sigma1 * sigma1 = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

/-- The second adjacent transposition squares to the identity in the `S₃` quotient. -/
theorem sigma2_sq :
    sigma2 * sigma2 = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

/-- The concrete `B₃ → S₃` generator assignment satisfies its only adjacent relation. -/
theorem s3ArtinGenerator_braid_relation :
    s3ArtinGenerator ⟨0, by decide⟩ * s3ArtinGenerator ⟨1, by decide⟩ *
        s3ArtinGenerator ⟨0, by decide⟩ =
      s3ArtinGenerator ⟨1, by decide⟩ * s3ArtinGenerator ⟨0, by decide⟩ *
        s3ArtinGenerator ⟨1, by decide⟩ := by
  simpa [s3ArtinGenerator_zero, s3ArtinGenerator_one] using s3_adjacent_artin_relation

/-- The concrete `B₃` permutation shadow packet. -/
theorem s3_artin_quotient_packet :
    s3ArtinGenerator ⟨0, by decide⟩ = Equiv.swap 0 1 ∧
    s3ArtinGenerator ⟨1, by decide⟩ = Equiv.swap 1 2 ∧
    sigma1 * sigma1 = 1 ∧
    sigma2 * sigma2 = 1 ∧
    s3ArtinGenerator ⟨0, by decide⟩ * s3ArtinGenerator ⟨1, by decide⟩ *
        s3ArtinGenerator ⟨0, by decide⟩ =
      s3ArtinGenerator ⟨1, by decide⟩ * s3ArtinGenerator ⟨0, by decide⟩ *
        s3ArtinGenerator ⟨1, by decide⟩ := by
  exact ⟨rfl, rfl, sigma1_sq, sigma2_sq, s3ArtinGenerator_braid_relation⟩

end InfoGeometry.Topology.ArtinBraidS3Quotient
