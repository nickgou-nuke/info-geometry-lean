import InfoGeometry.Topology.ArtinBraidS3Quotient
import Mathlib.GroupTheory.Perm.Fin

/-!
# Legacy name for the `B₃ → S₃` quotient anchor

This module is retained as a compatibility wrapper.  The authoritative owner is
`InfoGeometry.Topology.ArtinBraidS3Quotient`.

It is a Coxeter/permutation quotient obtained by imposing `sigma_i^2 = 1`; it is
not the genuine Fibonacci F/R braid representation.
-/

namespace AnyonBraidRepresentation

open InfoGeometry.Topology.ArtinBraidS3Quotient

/-- Compatibility alias for the `S₃` quotient target. -/
abbrev S3 := Equiv.Perm (Fin 3)

/-- Compatibility alias for the first quotient generator. -/
abbrev sigma1 : S3 := InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1

/-- Compatibility alias for the second quotient generator. -/
abbrev sigma2 : S3 := InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2

/-- Compatibility re-export of the `S₃` quotient Artin relation. -/
theorem s3_braid_relation :
    sigma1 * sigma2 * sigma1 = sigma2 * sigma1 * sigma2 := by
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.s3_adjacent_artin_relation

/-- Compatibility re-export: first generator squares to identity in the quotient. -/
theorem s3_projective_closure_one : sigma1 * sigma1 = 1 := by
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1_sq

/-- Compatibility re-export: second generator squares to identity in the quotient. -/
theorem s3_projective_closure_two : sigma2 * sigma2 = 1 := by
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2_sq

end AnyonBraidRepresentation
