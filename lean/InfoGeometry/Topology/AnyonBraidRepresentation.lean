import InfoGeometry.Topology.ArtinBraidS3Quotient

/-!
# Legacy name for the `B₃ → S₃` quotient anchor

This module is retained as a compatibility wrapper.  The authoritative owner is
`InfoGeometry.Topology.ArtinBraidS3Quotient`.

It is a Coxeter/permutation quotient obtained by imposing `sigma_i^2 = 1`; it is
not the genuine Fibonacci F/R braid representation.
-/

namespace InfoGeometry.Topology.AnyonBraidRepresentation

open InfoGeometry.Topology.ArtinBraidS3Quotient

/-- Compatibility alias for the `S₃` quotient target. -/
abbrev S3 := ArtinBraidS3Quotient.S3

/-- Compatibility alias for the first quotient generator. -/
def sigma1 : S3 := ArtinBraidS3Quotient.sigma1

/-- Compatibility alias for the second quotient generator. -/
def sigma2 : S3 := ArtinBraidS3Quotient.sigma2

/-- Compatibility re-export of the `S₃` quotient Artin relation. -/
theorem s3_braid_relation :
    sigma1 * sigma2 * sigma1 = sigma2 * sigma1 * sigma2 := by
  exact ArtinBraidS3Quotient.s3_is_artin_quotient

/-- Compatibility re-export: first generator squares to identity in the quotient. -/
theorem s3_projective_closure_one : sigma1 * sigma1 = 1 := by
  exact ArtinBraidS3Quotient.s3_generator_square_one_left

/-- Compatibility re-export: second generator squares to identity in the quotient. -/
theorem s3_projective_closure_two : sigma2 * sigma2 = 1 := by
  exact ArtinBraidS3Quotient.s3_generator_square_one_right

end InfoGeometry.Topology.AnyonBraidRepresentation
