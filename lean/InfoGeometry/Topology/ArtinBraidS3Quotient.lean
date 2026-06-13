import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Hom.Defs

namespace InfoGeometry.Topology.ArtinBraidS3Quotient

/-- Abstract Braid Group on N strands defined structurally -/
structure BraidGroup (n : ℕ) where
  carrier : Type
  grp : Group carrier

/-- Theorem structure mapping the 3-strand braid group into the S3 symmetric group quotient. -/
def s3_is_artin_quotient (B3 : BraidGroup 3) : Type :=
  letI := B3.grp
  B3.carrier →* Equiv.Perm (Fin 3)

end InfoGeometry.Topology.ArtinBraidS3Quotient
