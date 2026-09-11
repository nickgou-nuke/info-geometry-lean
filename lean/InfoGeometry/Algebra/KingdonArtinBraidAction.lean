import InfoGeometry.Topology.ArtinBraidS3Quotient
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Kingdon Artin braid permutation shadow

This file records only the finite `B₃ → S₃` permutation shadow used by the
Petersson isotope lane. It does not claim a linear action on the abstract
Kingdon carrier.
-/

namespace InfoGeometry.Algebra.KingdonArtinBraid

/-- The first adjacent braid generator as the `S₃` transposition `(0 1)`. -/
abbrev sigma1 : Equiv.Perm (Fin 3) :=
  InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1

/-- The second adjacent braid generator as the `S₃` transposition `(1 2)`. -/
abbrev sigma2 : Equiv.Perm (Fin 3) :=
  InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2

@[simp] theorem sigma1_sq : sigma1 * sigma1 = 1 := by
  simpa [sigma1] using InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1_sq

@[simp] theorem sigma2_sq : sigma2 * sigma2 = 1 := by
  simpa [sigma2] using InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2_sq

/-- The finite `S₃` braid shadow satisfies the Artin relation. -/
theorem kingdon_braid_relation :
    sigma1 * sigma2 * sigma1 = sigma2 * sigma1 * sigma2 := by
  simpa [sigma1, sigma2] using
    InfoGeometry.Topology.ArtinBraidS3Quotient.s3_adjacent_artin_relation

/-- Pointwise braid readback in the finite permutation shadow. -/
theorem kingdon_braid_relation_equiv :
    sigma1 * sigma2 * sigma1 = sigma2 * sigma1 * sigma2 := by
  exact kingdon_braid_relation

end InfoGeometry.Algebra.KingdonArtinBraid
