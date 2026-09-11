import InfoGeometry.Topology.ArtinBraidS3Quotient
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.Perm.Fin

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
abbrev S3 := Equiv.Perm (Fin 3)

/-- Compatibility alias for the first quotient generator. -/
abbrev sigma1 : S3 := InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1

/-- Compatibility alias for the second quotient generator. -/
abbrev sigma2 : S3 := InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2

/-! These are declaration aliases, not new theorem wrappers. -/
alias s3_braid_relation :=
  InfoGeometry.Topology.ArtinBraidS3Quotient.s3_adjacent_artin_relation

alias s3_projective_closure_one :=
  InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1_sq

alias s3_projective_closure_two :=
  InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2_sq

end InfoGeometry.Topology.AnyonBraidRepresentation
