import InfoGeometry.Algebra.KingdonHypebasis
import InfoGeometry.Topology.ArtinBraidS3Quotient

noncomputable section

/-!
# Artin braid action on the abstract Kingdon split octonion

This module transports the concrete adjacent-transposition quotient
`B₃ → S₃` to the eight-dimensional `AbstractKingdon` carrier.  The action fixes
both diagonal Peirce coordinates and simultaneously reindexes the upper and
lower three-coordinate sectors.

The construction is a real-linear `S₃` quotient action.  It does not claim that
these odd coordinate permutations preserve the split-octonion multiplication,
construct a tensor-product `R`-matrix, trivialize the octonion associator, or
identify the stabilizer with real split `G₂`.
-/

namespace InfoGeometry.Algebra.KingdonArtinBraid

open InfoGeometry.Algebra.KingdonSplitOctonion
open InfoGeometry.Physics.ZornMatrixSU3

/-- Reindex a three-coordinate vector by a permutation. -/
def permuteThree (p : Equiv.Perm (Fin 3)) : ThreeSpace ≃ₗ[ℝ] ThreeSpace where
  toFun u := fun i => u (p.symm i)
  invFun u := fun i => u (p i)
  left_inv u := by
    funext i
    simp
  right_inv u := by
    funext i
    simp
  map_add' u v := by
    funext i
    rfl
  map_smul' r u := by
    funext i
    rfl

/-- Simultaneous permutation of the upper and lower Peirce vector coordinates. -/
def zornCoordinatePermutation (p : Equiv.Perm (Fin 3)) : ZornMatrix ≃ₗ[ℝ] ZornMatrix where
  toFun X := ⟨X.a, X.b, permuteThree p X.x, permuteThree p X.y⟩
  invFun X := ⟨X.a, X.b, permuteThree p.symm X.x, permuteThree p.symm X.y⟩
  left_inv X := by
    apply InfoGeometry.Physics.ZornMatrixSU3.ext <;> simp [permuteThree]
  right_inv X := by
    apply InfoGeometry.Physics.ZornMatrixSU3.ext <;> simp [permuteThree]
  map_add' X Y := by
    apply InfoGeometry.Physics.ZornMatrixSU3.ext <;> rfl
  map_smul' r X := by
    apply InfoGeometry.Physics.ZornMatrixSU3.ext <;> rfl

/-- Transport the explicit Peirce-coordinate permutation to the abstract Kingdon carrier. -/
def kingdonCoordinatePermutation (p : Equiv.Perm (Fin 3)) :
    AbstractKingdon ≃ₗ[ℝ] AbstractKingdon :=
  kingdonZornLinearEquiv.trans
    ((zornCoordinatePermutation p).trans kingdonZornLinearEquiv.symm)

@[simp] theorem realization_kingdonCoordinatePermutation
    (p : Equiv.Perm (Fin 3)) (x : AbstractKingdon) :
    realization (kingdonCoordinatePermutation p x) =
      zornCoordinatePermutation p (realization x) := by
  simp [kingdonCoordinatePermutation]

/-- The coordinate action preserves the upper Peirce vector sector. -/
@[simp] theorem kingdonCoordinatePermutation_upper
    (p : Equiv.Perm (Fin 3)) (v : ThreeSpace) :
    kingdonCoordinatePermutation p (upper v) = upper (permuteThree p v) := by
  apply realization_injective
  simp [zornCoordinatePermutation]

/-- The coordinate action preserves the lower Peirce vector sector. -/
@[simp] theorem kingdonCoordinatePermutation_lower
    (p : Equiv.Perm (Fin 3)) (v : ThreeSpace) :
    kingdonCoordinatePermutation p (lower v) = lower (permuteThree p v) := by
  apply realization_injective
  simp [zornCoordinatePermutation]

/-- The upper diagonal Peirce idempotent is fixed by every coordinate permutation. -/
@[simp] theorem kingdonCoordinatePermutation_diagonalUpper
    (p : Equiv.Perm (Fin 3)) :
    kingdonCoordinatePermutation p diagonalUpper = diagonalUpper := by
  apply realization_injective
  simp [zornCoordinatePermutation, permuteThree, projector1]

/-- The lower diagonal Peirce idempotent is fixed by every coordinate permutation. -/
@[simp] theorem kingdonCoordinatePermutation_diagonalLower
    (p : Equiv.Perm (Fin 3)) :
    kingdonCoordinatePermutation p diagonalLower = diagonalLower := by
  apply realization_injective
  simp [zornCoordinatePermutation, permuteThree, projector2]

/-- The Kingdon-space image of the first adjacent Artin generator. -/
def sigma1 : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon :=
  kingdonCoordinatePermutation InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1

/-- The Kingdon-space image of the second adjacent Artin generator. -/
def sigma2 : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon :=
  kingdonCoordinatePermutation InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2

@[simp] theorem permuteThree_sigma1_basisVec_zero :
    permuteThree InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 (basisVec 0) =
      basisVec 1 := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem permuteThree_sigma1_basisVec_one :
    permuteThree InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 (basisVec 1) =
      basisVec 0 := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem permuteThree_sigma1_basisVec_two :
    permuteThree InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 (basisVec 2) =
      basisVec 2 := by
  funext i
  fin_cases i <;> rfl

/-- The permutation quotient action is not an octonion-algebra action. -/
theorem sigma1_not_multiplicative :
    ∃ x y : AbstractKingdon, sigma1 (x * y) ≠ sigma1 x * sigma1 y := by
  refine ⟨upper (basisVec 0), upper (basisVec 1), ?_⟩
  intro h
  simp only [upper_basisVec_zero_mul_one, sigma1,
    kingdonCoordinatePermutation_upper, kingdonCoordinatePermutation_lower,
    permuteThree_sigma1_basisVec_zero, permuteThree_sigma1_basisVec_one,
    permuteThree_sigma1_basisVec_two, upper_basisVec_one_mul_zero] at h
  have hreal := congrArg (fun z : AbstractKingdon => realization z) h
  dsimp only at hreal
  rw [realization_lower, map_neg, realization_lower] at hreal
  have hy := congrArg (fun X : ZornMatrix => X.y 2) hreal
  change (1 : ℝ) = -1 at hy
  norm_num at hy

/-- Native Reidemeister-III/Artin relation on the abstract Kingdon space. -/
theorem kingdon_braid_relation_equiv :
    sigma1.trans (sigma2.trans sigma1) =
      sigma2.trans (sigma1.trans sigma2) := by
  apply LinearEquiv.ext
  intro x
  apply realization_injective
  simp only [sigma1, sigma2, LinearEquiv.trans_apply,
    realization_kingdonCoordinatePermutation]
  apply InfoGeometry.Physics.ZornMatrixSU3.ext <;> try rfl
  all_goals
    funext i
    fin_cases i <;> rfl

/-- Pointwise form of the native Kingdon Artin braid relation. -/
theorem kingdon_braid_relation (x : AbstractKingdon) :
    sigma1 (sigma2 (sigma1 x)) = sigma2 (sigma1 (sigma2 x)) := by
  exact LinearEquiv.congr_fun kingdon_braid_relation_equiv x

end InfoGeometry.Algebra.KingdonArtinBraid
