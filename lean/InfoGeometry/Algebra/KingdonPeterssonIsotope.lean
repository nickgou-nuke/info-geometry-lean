import InfoGeometry.Algebra.KingdonArtinBraidAction

noncomputable section

/-!
# Petersson isotope of the abstract Kingdon split octonions

This file uses the even three-cycle in the coordinate `S₃` action as a genuine
order-three split-octonion automorphism `ρ`. The Petersson product is

`x ⋆ y = ρ(conj x) * ρ²(conj y)`.

It is a concrete owner-level construction, not a generic twist-algebra wrapper.
-/

namespace InfoGeometry.Algebra.KingdonPetersson

open InfoGeometry.Algebra.KingdonSplitOctonion
open InfoGeometry.Algebra.KingdonArtinBraid
open InfoGeometry.Physics.ZornMatrixSU3

abbrev AK := AbstractKingdon

/-- The even three-cycle obtained from the two adjacent Artin generators. -/
def peterssonCyclePermutation : Equiv.Perm (Fin 3) :=
  InfoGeometry.Topology.ArtinBraidS3Quotient.sigma1 *
    InfoGeometry.Topology.ArtinBraidS3Quotient.sigma2

@[simp] theorem peterssonCyclePermutation_zero : peterssonCyclePermutation 0 = 1 := rfl
@[simp] theorem peterssonCyclePermutation_one : peterssonCyclePermutation 1 = 2 := rfl
@[simp] theorem peterssonCyclePermutation_two : peterssonCyclePermutation 2 = 0 := rfl
@[simp] theorem peterssonCyclePermutation_symm_zero : peterssonCyclePermutation.symm 0 = 2 := rfl
@[simp] theorem peterssonCyclePermutation_symm_one : peterssonCyclePermutation.symm 1 = 0 := rfl
@[simp] theorem peterssonCyclePermutation_symm_two : peterssonCyclePermutation.symm 2 = 1 := rfl

/-- The real-linear order-three map used in the Petersson isotope. -/
noncomputable def peterssonCycle : AK ≃ₗ[ℝ] AK :=
  kingdonCoordinatePermutation peterssonCyclePermutation

@[simp] theorem realization_peterssonCycle (x : AK) :
    realization (peterssonCycle x) =
      zornCoordinatePermutation peterssonCyclePermutation (realization x) :=
  realization_kingdonCoordinatePermutation _ _

/-- The even coordinate cycle is a genuine split-octonion automorphism. -/
@[simp] theorem peterssonCycle_mul (x y : AK) :
    peterssonCycle (x * y) = peterssonCycle x * peterssonCycle y := by
  apply realization_injective
  simp only [realization_peterssonCycle, map_mul]
  ext i <;> simp [zornCoordinatePermutation, permuteThree,
    InfoGeometry.Physics.ZornMatrixSU3.mul,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
    ZornVectorMatrixExplicit.dot3,
    ZornVectorMatrixExplicit.cross3]
  all_goals (try fin_cases i)
  all_goals try simp
  all_goals ring

@[simp] theorem peterssonCycle_order_three (x : AK) :
    peterssonCycle (peterssonCycle (peterssonCycle x)) = x := by
  apply realization_injective
  simp only [realization_peterssonCycle]
  apply InfoGeometry.Physics.ZornMatrixSU3.ext <;> try rfl
  all_goals
    funext i
    fin_cases i <;> rfl

@[simp] theorem peterssonCycle_norm (x : AK) :
    kingdonNorm (peterssonCycle x) = kingdonNorm x := by
  simp only [kingdonNorm, realization_peterssonCycle]
  simp [InfoGeometry.Physics.ZornMatrixSU3.norm,
    zornCoordinatePermutation, permuteThree,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    ZornVectorMatrixExplicit.dot3]
  ring

@[simp] theorem peterssonCycle_polar (x y : AK) :
    kingdonPolar (peterssonCycle x) (peterssonCycle y) =
      kingdonPolar x y := by
  unfold kingdonPolar
  rw [← map_add]
  simp only [peterssonCycle_norm]

@[simp] theorem peterssonCycle_conjugate (x : AK) :
    peterssonCycle (kingdonConjugate x) =
      kingdonConjugate (peterssonCycle x) := by
  apply realization_injective
  simp only [realization_peterssonCycle, realization_kingdonConjugate]
  apply InfoGeometry.Physics.ZornMatrixSU3.ext <;> rfl

/-- The Petersson isotope product `x ⋆ y = ρ(conj x) * ρ²(conj y)`. -/
def peterssonMul (x y : AK) : AK :=
  peterssonCycle (kingdonConjugate x) *
    peterssonCycle (peterssonCycle (kingdonConjugate y))

theorem peterssonMul_add_left (x y z : AK) :
    peterssonMul (x + y) z = peterssonMul x z + peterssonMul y z := by
  simp [peterssonMul, add_mul]

theorem peterssonMul_smul_left (r : ℝ) (x y : AK) :
    peterssonMul (r • x) y = r • peterssonMul x y := by
  simp only [peterssonMul, kingdonConjugate_smul, map_smul]
  apply realization_injective
  simp only [map_mul, realization_smul]
  exact InfoGeometry.Physics.ZornMatrixSU3.smul_mul_zorn _ _ _

theorem peterssonMul_add_right (x y z : AK) :
    peterssonMul x (y + z) = peterssonMul x y + peterssonMul x z := by
  simp [peterssonMul, mul_add]

theorem peterssonMul_smul_right (r : ℝ) (x y : AK) :
    peterssonMul x (r • y) = r • peterssonMul x y := by
  simp only [peterssonMul, kingdonConjugate_smul, map_smul]
  apply realization_injective
  simp only [map_mul, realization_smul]
  exact InfoGeometry.Physics.ZornMatrixSU3.mul_smul_zorn _ _ _

/-- The Petersson multiplication as a bundled real-bilinear map. -/
noncomputable def peterssonMulBilin : AK →ₗ[ℝ] AK →ₗ[ℝ] AK :=
  LinearMap.mk₂ ℝ peterssonMul peterssonMul_add_left
    peterssonMul_smul_left peterssonMul_add_right peterssonMul_smul_right

@[simp] theorem peterssonMulBilin_apply (x y : AK) :
    peterssonMulBilin x y = peterssonMul x y := rfl

/-- The Petersson isotope retains the original split composition norm. -/
@[simp] theorem peterssonNorm_mul (x y : AK) :
    kingdonNorm (peterssonMul x y) = kingdonNorm x * kingdonNorm y := by
  rw [peterssonMul, kingdonNorm_mul, peterssonCycle_norm,
    kingdonNorm_conjugate, peterssonCycle_norm, peterssonCycle_norm,
    kingdonNorm_conjugate]

/-- Exact compatibility of the original involution with the Petersson product. -/
@[simp] theorem peterssonConjugate_mul (x y : AK) :
    kingdonConjugate (peterssonMul x y) =
      peterssonCycle (peterssonCycle y) * peterssonCycle x := by
  rw [peterssonMul, kingdonConjugate_mul]
  simp only [← peterssonCycle_conjugate, kingdonConjugate_involutive]

/-- The Petersson product is associative with respect to the polar form. This,
together with `peterssonNorm_mul`, is the defining symmetric-composition law. -/
theorem peterssonPolar_assoc (x y z : AK) :
    kingdonPolar (peterssonMul x y) z =
      kingdonPolar x (peterssonMul y z) := by
  rw [kingdonPolar_coordinate, kingdonPolar_coordinate]
  simp only [peterssonMul, map_mul, realization_peterssonCycle,
    realization_kingdonConjugate]
  simp [zornCoordinatePermutation, permuteThree, conjugate,
    InfoGeometry.Physics.ZornMatrixSU3.mul,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
    ZornVectorMatrixExplicit.dot3,
    ZornVectorMatrixExplicit.cross3]
  ring

theorem peterssonPolarBilin_assoc (x y z : AK) :
    kingdonPolarBilin (peterssonMul x y) z =
      kingdonPolarBilin x (peterssonMul y z) :=
  peterssonPolar_assoc x y z

/-- Closed symmetric-composition packet for the concrete Petersson isotope. -/
theorem petersson_symmetric_composition :
    (∀ x y : AK,
      kingdonNorm (peterssonMul x y) = kingdonNorm x * kingdonNorm y) ∧
    (∀ x y z : AK,
      kingdonPolar (peterssonMul x y) z = kingdonPolar x (peterssonMul y z)) ∧
    (∀ x : AK, (∀ y : AK, kingdonPolar x y = 0) → x = 0) := by
  exact ⟨peterssonNorm_mul, peterssonPolar_assoc, kingdonPolar_nondegenerate⟩

end InfoGeometry.Algebra.KingdonPetersson
