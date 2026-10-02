import InfoGeometry.Categorical.BraidThreePresentedGroup
import InfoGeometry.Topology.ArtinBraidS3Quotient
import Mathlib.Tactic

/-!
# Canonical Artin braid-group quotient B₃ → S₃

The repository already has:

* the genuine presented three-strand Artin braid group
  `BraidThreePresentedGroup.BraidGroup3`;
* the concrete adjacent transpositions in `S₃` satisfying the Artin relation.

This module connects those two owners through the universal property of the
presented group.  It therefore upgrades the old finite "quotient shadow" to an
actual group homomorphism.

No faithfulness statement is made: the map is the standard permutation
quotient, so the pure braid subgroup lies in its kernel.
-/

namespace InfoGeometry.Categorical.BraidGroup3S3QuotientBridge

open InfoGeometry.Categorical.BraidThreePresentedGroup
open InfoGeometry.Topology.ArtinBraidS3Quotient

/-- The two adjacent transpositions form genuine Artin data in `S₃`. -/
def s3ArtinPair : ArtinPair (Equiv.Perm (Fin 3)) where
  sigmaOne := InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1
  sigmaTwo := InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2
  artin := s3_adjacent_artin_relation

/-- The canonical permutation quotient of the three-strand Artin braid group. -/
def braidGroup3ToS3 :
    BraidGroup3 →* Equiv.Perm (Fin 3) :=
  s3ArtinPair.toBraidGroupHom

@[simp] theorem braidGroup3ToS3_sigmaOne :
    braidGroup3ToS3
        InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaOne =
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 := by
  exact ArtinPair.toBraidGroupHom_sigmaOne s3ArtinPair

@[simp] theorem braidGroup3ToS3_sigmaTwo :
    braidGroup3ToS3
        InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaTwo =
      InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 := by
  exact ArtinPair.toBraidGroupHom_sigmaTwo s3ArtinPair

/-- The squares of the Artin generators lie in the permutation-kernel. -/
theorem sigmaOne_sq_mem_kernel :
    InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaOne ^ 2 ∈
      braidGroup3ToS3.ker := by
  change braidGroup3ToS3
      (InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaOne ^ 2) = 1
  rw [map_pow, braidGroup3ToS3_sigmaOne]
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1_sq

theorem sigmaTwo_sq_mem_kernel :
    InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaTwo ^ 2 ∈
      braidGroup3ToS3.ker := by
  change braidGroup3ToS3
      (InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaTwo ^ 2) = 1
  rw [map_pow, braidGroup3ToS3_sigmaTwo]
  exact InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2_sq

/-- The normal closure of the generator squares is contained in the kernel of
the permutation quotient. -/
theorem involution_normalClosure_le_kernel :
    Subgroup.normalClosure
        ({InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaOne ^ 2,
          InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaTwo ^ 2} :
          Set BraidGroup3) ≤
      braidGroup3ToS3.ker := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rcases hx with rfl | rfl
  · exact sigmaOne_sq_mem_kernel
  · exact sigmaTwo_sq_mem_kernel

/-- The standard Garside element maps to the transposition swapping the first
and third strands. -/
theorem garsideDelta_maps_to_outer_swap :
    braidGroup3ToS3 garsideDelta = Equiv.swap (0 : Fin 3) 2 := by
  change
    InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2 *
        InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 =
      Equiv.swap (0 : Fin 3) 2
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

end InfoGeometry.Categorical.BraidGroup3S3QuotientBridge
