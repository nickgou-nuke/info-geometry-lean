/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Canonical.RealSpacetime4x4Closure
import InfoGeometry.Parafermion.TetractysPoincareSupersymmetryTwistorPoset
import Mathlib.Tactic

/-!
# Real Peirce translations in the Koszul-graded soldering algebra

The real soldering owner identifies `FourSpace` with `M₂(ℝ)` and proves that
the determinant is its split-signature `(2,2)` quadratic form. This module
inserts that matrix into an actual upper Peirce corner of `M₂(M₂(ℝ))`, the representation
of the repository's Koszul-graded tensor
`Cl(1,1) ᵍ⊗ M₂(ℝ)`.  The resulting translation operators are square-zero,
pairwise product-zero, additive, and have the owner's split-signature `(2,2)`
determinant as their soldering readout. Physical `(+---)` Minkowski vectors
enter separately through `RealSpacetime4x4Closure` and its real `J4`-commuting
Pauli representation below.

This is a finite-dimensional real operator bridge. It identifies the
anticommutator of the two real Peirce charges with the diagonal real momentum
operator in the genuine two-factor Koszul-graded matrix tensor. It does not
claim that the separate complex-valued Cuntz
`ChiralOperatorPresentation` is thereby represented.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge

open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.GradedTensorWeylBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita
open InfoGeometry.Parafermion.TetractysPoincareSupersymmetryTwistorPoset
open Matrix
open scoped TensorProduct GradedTensorProduct

local notation "M2R" => Matrix (Fin 2) (Fin 2) ℝ
local notation "FourSpace" => InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace
local notation "GradedSolder" => twoMatrixGradedTensor

/-- The real soldering coefficient carrier is genuinely noncommutative:
the matrix units `E₀₀` and `E₀₁` have different products in the two orders. -/
theorem realSolderingM2_noncommutative :
    ∃ A C : Matrix (Fin 2) (Fin 2) ℝ, A * C ≠ C * A := by
  refine ⟨Matrix.single 0 0 1, Matrix.single 0 1 1, ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Matrix.single] at h01

/-- The upper Peirce-corner matrix representing a real soldered four-vector. -/
def translationBlock (p : FourSpace) : Matrix (Fin 2) (Fin 2) M2R :=
  !![0, realMomentum p; 0, 0]

/-- The idempotent selecting the first Peirce sheet of the nested real
matrix carrier. -/
def translationPeirceIdem : Matrix (Fin 2) (Fin 2) M2R := !![1, 0; 0, 0]

/-- The translation block is exactly the upper-corner Peirce projection of
the real momentum soldering matrix. -/
theorem translationBlock_eq_corner (p : FourSpace) :
    translationBlock p =
      TransN translationPeirceIdem (translationBlock p) := by
  unfold TransN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translationPeirceIdem, translationBlock,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Two soldered translations have zero product in the upper Peirce corner. -/
theorem translationBlock_mul_eq_zero (p q : FourSpace) :
    translationBlock p * translationBlock q = 0 := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [translationBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- The real translation block depends additively on its four-vector. -/
theorem translationBlock_add (p q : FourSpace) :
    translationBlock (p + q) = translationBlock p + translationBlock q := by
  have hv : fourSpaceEquivVec22 (p + q) =
      fourSpaceEquivVec22 p + fourSpaceEquivVec22 q :=
    fourSpaceEquivVec22.map_add p q
  have hm : realMomentum (p + q) = realMomentum p + realMomentum q := by
    unfold realMomentum
    rw [hv]
    exact InfoGeometry.Clifford.Soldering.soldering.map_add _ _
  rw [translationBlock, hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [translationBlock]

/-- The native `M₂(ℝ) ᵍ⊗ M₂(ℝ)` element whose Morita image is the real
translation block. Its carrier is the genuine Koszul product, not the
ungraded tensor product. -/
def translationInGradedTensor (p : FourSpace) : GradedSolder :=
  twoMatrixGradedTensorMoritaEquiv.symm (translationBlock p)

@[simp] theorem translationInGradedTensor_representation (p : FourSpace) :
    twoMatrixGradedTensorMoritaEquiv (translationInGradedTensor p) = translationBlock p :=
  twoMatrixGradedTensorMoritaEquiv.apply_symm_apply _

/-- The Peirce translation is the first odd matrix unit tensored with the
parity-conjugated real momentum matrix.  Under the native graded Morita map,
the Koszul-twisted tail parity cancels that conjugation and places precisely
`realMomentum p` in the upper-right block. -/
theorem translationInGradedTensor_eq_odd_tmul (p : FourSpace) :
    translationInGradedTensor p =
      (matrixE01 ᵍ⊗ₜ[ℝ] matrixParity (realMomentum p) : GradedSolder) := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [translationInGradedTensor_representation,
    twoMatrixGradedTensorMoritaEquiv_tmul]
  have hhead :
      InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv.symm matrixE01 =
        InfoGeometry.Clifford.Cl11GradedTensorMorita.headUnit 0 1 := rfl
  rw [hhead]
  rw [InfoGeometry.Clifford.Cl11GradedTensorMorita.tensorMatrixEquiv_apply,
    InfoGeometry.Clifford.Cl11GradedTensorMorita.tensorToMatrix_tmul_matrix]
  have hparity : matrixParity (matrixParity (realMomentum p)) = realMomentum p :=
    InfoGeometry.Canonical.GradedTensorWeylBridge.matrixParity_involutive _
  rw [hparity]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [translationBlock,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.headUnit]

/-- The total product parity of a Peirce translation acts on its soldered
momentum coefficient by the second factor's checkerboard parity. This is the
Koszul/Jordan--Wigner correction in the existing graded tensor Morita model. -/
theorem translationInGradedTensor_parity (p : FourSpace) :
    twoMatrixParity (translationInGradedTensor p) =
      twoMatrixGradedTensorMoritaEquiv.symm
        (!![0, -matrixParity (realMomentum p); 0, 0] :
          Matrix (Fin 2) (Fin 2) M2R) := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [twoMatrixParity_apply, translationInGradedTensor_representation,
    AlgEquiv.apply_symm_apply]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [translationBlock, matrixGrade_apply, matrixParity_apply]

/-- The Peirce translation is odd in the total graded tensor exactly when
its real soldered momentum matrix is even under checkerboard parity. Arbitrary
four-space momenta therefore do not automatically define odd supercharges. -/
theorem translationInGradedTensor_odd_iff (p : FourSpace) :
    translationInGradedTensor p ∈ twoMatrixProductGrading 1 ↔
      matrixParity (realMomentum p) = realMomentum p := by
  constructor
  · intro h
    change twoMatrixParity (translationInGradedTensor p) =
      -translationInGradedTensor p at h
    have h' := congrArg twoMatrixGradedTensorMoritaEquiv h
    rw [translationInGradedTensor_parity, map_neg,
      translationInGradedTensor_representation,
      AlgEquiv.apply_symm_apply] at h'
    have hA := congrArg (fun M : Matrix (Fin 2) (Fin 2) M2R => M 0 1) h'
    simpa [translationBlock] using neg_injective hA
  · intro hA
    change twoMatrixParity (translationInGradedTensor p) =
      -translationInGradedTensor p
    apply twoMatrixGradedTensorMoritaEquiv.injective
    rw [twoMatrixParity_apply, translationInGradedTensor_representation]
    ext i j a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [translationBlock, matrixGrade_apply, matrixParity_apply, hA]

/-- The current Peirce translation family is not wholly odd: a pure spatial
`x` soldering vector has off-diagonal momentum matrix, which changes sign under
the coefficient parity. Thus the unconditional anticommutator identity above
does not by itself define four odd supertranslation charges. -/
theorem translationInGradedTensor_spatialX_not_odd :
    translationInGradedTensor
        (fourSpaceEquivVec22.symm (0, 0, 1, 0)) ∉ twoMatrixProductGrading 1 := by
  intro hodd
  have hpar := (translationInGradedTensor_odd_iff _).mp hodd
  have hcoords :
      fourSpaceEquivVec22 (fourSpaceEquivVec22.symm (0, 0, 1, 0)) =
        (0, 0, 1, 0) := by
    exact fourSpaceEquivVec22.apply_symm_apply _
  have hentry :
      realMomentum (fourSpaceEquivVec22.symm (0, 0, 1, 0)) 0 1 = 1 := by
    rw [realMomentum, hcoords]
    simpa using InfoGeometry.Clifford.SolderingIsomorphism.soldering_entry_01 0 0 1 0
  have hparityEntry := congrArg (fun M : M2R => M 0 1) hpar
  have hneg :
      -(realMomentum (fourSpaceEquivVec22.symm (0, 0, 1, 0)) 0 1) =
        realMomentum (fourSpaceEquivVec22.symm (0, 0, 1, 0)) 0 1 := by
    rw [matrixParity_apply] at hparityEntry
    simpa using hparityEntry
  rw [hentry] at hneg
  norm_num at hneg

/-- The complementary lower Peirce corner used as the second real charge. -/
def conjugatePeirceChargeBlock : Matrix (Fin 2) (Fin 2) M2R :=
  !![0, 0; 1, 0]

/-- Diagonal action of the soldered momentum matrix on both Peirce sheets. -/
def diagonalMomentumOperator (p : FourSpace) : Matrix (Fin 2) (Fin 2) M2R :=
  !![realMomentum p, 0; 0, realMomentum p]

/-- Native Koszul-graded tensor element for the lower Peirce charge. -/
def conjugatePeirceCharge : GradedSolder :=
  twoMatrixGradedTensorMoritaEquiv.symm conjugatePeirceChargeBlock

/-- The complementary Peirce charge is odd in the total grading. -/
theorem conjugatePeirceCharge_odd :
    conjugatePeirceCharge ∈ twoMatrixProductGrading 1 := by
  change twoMatrixParity conjugatePeirceCharge = -conjugatePeirceCharge
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [twoMatrixParity_apply, conjugatePeirceCharge,
    AlgEquiv.apply_symm_apply, map_neg, AlgEquiv.apply_symm_apply]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [conjugatePeirceChargeBlock, matrixGrade_apply, matrixParity_apply]

/-- In the real two-matrix superalgebra, the Peirce translation and its
complementary lower charge anticommute to the diagonal soldered momentum.
The identity is conditional as a supercharge statement: the first factor is
odd precisely on the checkerboard-even momentum subspace, as characterized
above. -/
theorem translationCharge_anticommutator_eq_diagonalMomentum (p : FourSpace) :
    translationInGradedTensor p * conjugatePeirceCharge +
      conjugatePeirceCharge * translationInGradedTensor p =
        twoMatrixGradedTensorMoritaEquiv.symm (diagonalMomentumOperator p) := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  simp only [map_add, map_mul, translationInGradedTensor_representation,
    conjugatePeirceCharge, AlgEquiv.apply_symm_apply]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [translationBlock, conjugatePeirceChargeBlock,
      diagonalMomentumOperator]

/-- The soldered real translation anticommutator also holds on the full
eight-dimensional doubled Hestenes–Krein carrier. The same four-dimensional
spinor operator acts on each Krein sheet through `doubleEnd`; no change of
scalar field or identification of the two carrier dimensions is made. -/
theorem doubledTranslationCharge_anticommutator_eq_diagonalMomentum
    (p : FourSpace) :
    doubleEnd (realTwoMatrixGradedTensorOnFourSpace (translationInGradedTensor p)) *
        doubleEnd (realTwoMatrixGradedTensorOnFourSpace conjugatePeirceCharge) +
      doubleEnd (realTwoMatrixGradedTensorOnFourSpace conjugatePeirceCharge) *
        doubleEnd (realTwoMatrixGradedTensorOnFourSpace (translationInGradedTensor p)) =
        doubleEnd (realTwoMatrixGradedTensorOnFourSpace
          (twoMatrixGradedTensorMoritaEquiv.symm (diagonalMomentumOperator p))) := by
  calc
    _ = doubleEnd
        (realTwoMatrixGradedTensorOnFourSpace (translationInGradedTensor p) *
          realTwoMatrixGradedTensorOnFourSpace conjugatePeirceCharge +
        realTwoMatrixGradedTensorOnFourSpace conjugatePeirceCharge *
          realTwoMatrixGradedTensorOnFourSpace (translationInGradedTensor p)) := by
      rw [doubleEnd_add, doubleEnd_mul, doubleEnd_mul]
    _ = doubleEnd (realTwoMatrixGradedTensorOnFourSpace
        (twoMatrixGradedTensorMoritaEquiv.symm (diagonalMomentumOperator p))) := by
      have hE (A B : GradedSolder) :
          realTwoMatrixGradedTensorOnFourSpace (A * B + B * A) =
            realTwoMatrixGradedTensorOnFourSpace A *
              realTwoMatrixGradedTensorOnFourSpace B +
            realTwoMatrixGradedTensorOnFourSpace B *
              realTwoMatrixGradedTensorOnFourSpace A := by
        calc
          _ = realTwoMatrixGradedTensorOnFourSpace (A * B) +
              realTwoMatrixGradedTensorOnFourSpace (B * A) :=
            map_add realTwoMatrixGradedTensorOnFourSpace _ _
          _ = _ := by rw [map_mul, map_mul]
      rw [← hE]
      exact congrArg (fun z => doubleEnd (realTwoMatrixGradedTensorOnFourSpace z))
        (translationCharge_anticommutator_eq_diagonalMomentum p)

/-- The same translation/charge anticommutator is represented inside the
three-mode real CAR algebra through the injective diagonal two-mode
embedding. This is the algebra-level bridge from the Peirce translation
sector to the full circular three-channel carrier. -/
theorem threeMode_translationCharge_anticommutator_eq_diagonalMomentum
    (p : FourSpace) :
    twoModeIntoThreeMode (translationInGradedTensor p) *
        twoModeIntoThreeMode conjugatePeirceCharge +
      twoModeIntoThreeMode conjugatePeirceCharge *
        twoModeIntoThreeMode (translationInGradedTensor p) =
      twoModeIntoThreeMode
        (twoMatrixGradedTensorMoritaEquiv.symm (diagonalMomentumOperator p)) := by
  have h := congrArg twoModeIntoThreeMode
    (translationCharge_anticommutator_eq_diagonalMomentum p)
  simpa only [map_add, map_mul] using h

/-- On the actual eight-dimensional doubled Krein carrier, the three-mode
representation of the embedded translation and charge operators has the
same anticommutator as the diagonal momentum operator. -/
theorem realThreeKrein_translationCharge_anticommutator_eq_diagonalMomentum
    (p : FourSpace) :
    realThreeMatrixTensorOnH4 (twoModeIntoThreeMode (translationInGradedTensor p)) *
        realThreeMatrixTensorOnH4 (twoModeIntoThreeMode conjugatePeirceCharge) +
      realThreeMatrixTensorOnH4 (twoModeIntoThreeMode conjugatePeirceCharge) *
        realThreeMatrixTensorOnH4 (twoModeIntoThreeMode (translationInGradedTensor p)) =
      realThreeMatrixTensorOnH4 (twoModeIntoThreeMode
        (twoMatrixGradedTensorMoritaEquiv.symm (diagonalMomentumOperator p))) := by
  have h := congrArg realThreeMatrixTensorOnH4
    (threeMode_translationCharge_anticommutator_eq_diagonalMomentum p)
  simpa only [map_add, map_mul] using h

/-- Translation generators square to zero in the real graded tensor carrier. -/
theorem translationInGradedTensor_square (p : FourSpace) :
    translationInGradedTensor p * translationInGradedTensor p = 0 := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [map_mul, map_zero, translationInGradedTensor_representation]
  exact translationBlock_mul_eq_zero p p

/-- Distinct translations have zero ordered product in the same Peirce
corner. -/
theorem translationInGradedTensor_mul (p q : FourSpace) :
    translationInGradedTensor p * translationInGradedTensor q = 0 := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [map_mul, map_zero, translationInGradedTensor_representation,
    translationInGradedTensor_representation]
  exact translationBlock_mul_eq_zero p q

/-- The graded-tensor representation preserves addition of translation
parameters. -/
theorem translationInGradedTensor_add (p q : FourSpace) :
    translationInGradedTensor (p + q) =
      translationInGradedTensor p + translationInGradedTensor q := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [map_add, translationInGradedTensor_representation,
    translationInGradedTensor_representation,
    translationInGradedTensor_representation]
  exact translationBlock_add p q

/-- The upper Peirce translations form an additive subgroup law under
`(1 + T p) (1 + T q) = 1 + T (p + q)`. -/
theorem translationBlock_affine_comp (p q : FourSpace) :
    (1 + translationBlock p) * (1 + translationBlock q) =
      1 + translationBlock (p + q) := by
  calc
    (1 + translationBlock p) * (1 + translationBlock q) =
        1 + translationBlock p + translationBlock q +
          translationBlock p * translationBlock q := by noncomm_ring
    _ = 1 + translationBlock (p + q) := by
      rw [translationBlock_mul_eq_zero, translationBlock_add]
      abel

/-- The soldering determinant of the translation block's upper-right entry
is the split-signature `(2,2)` quadratic form owned by the real soldering
bridge. It is not identified here with the DeWitt `(-,+,+,+)` form. -/
theorem translationBlock_det (p : FourSpace) :
    (translationBlock p 0 1).det =
      InfoGeometry.Clifford.Soldering.q22 (fourSpaceEquivVec22 p) := by
  simpa [translationBlock] using realMomentum_det p

/-- Coordinate expansion of the split-signature determinant readout. -/
theorem translationBlock_det_coordinates (p : FourSpace) :
    (translationBlock p 0 1).det =
      let v := fourSpaceEquivVec22 p
      v.1 ^ 2 - (v.2.1) ^ 2 - (v.2.2.1) ^ 2 + (v.2.2.2) ^ 2 := by
  rw [translationBlock_det]
  rcases fourSpaceEquivVec22 p with ⟨t, z, x, y⟩
  exact InfoGeometry.Clifford.Soldering.q22_apply t z x y

/-- The Hestenes realification of a Hermitian Pauli spacetime vector obeys
its quadratic characteristic equation. Here the real complex structure is
the owner matrix `J4`; the scalar invariant is the physical `(+---)` interval,
not the split `(2,2)` determinant of a single real `2×2` soldering matrix. -/
theorem realHermitianPauli_cayleyHamilton
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let M := InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X
    M * M - (2 * X.t) • M +
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X •
        (1 : Matrix (Fin 4) (Fin 4) ℝ) = 0 := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix,
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval] <;>
    ring

/-- The same realified spacetime representative commutes with the Hestenes
complex-structure operator. This records the real-linear `J`-structure and
does not change the scalar field to `ℂ`. -/
theorem realHermitianPauli_commutes_with_J4
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X *
        InfoGeometry.Canonical.RealSpacetime4x4Closure.J4 =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.J4 *
        InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X :=
  InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix_commutes_J X

/-! ### Signature-correct real graded tensor factors

The checkerboard grading on both matrix factors gives a split `(2,2)` model.
For the real Minkowski `(3,1)` Clifford signs, use the native
`Cl(1,1)`-graded tensor with a real `M₂(ℝ)` coefficient algebra graded by
conjugation with the Hestenes complex-structure matrix `epsilon`. The two
odd tail generators below square to `+1` and anticommute. -/

/-- The involutive real matrix automorphism `A ↦ epsilon * A * (-epsilon)`. -/
def hestenesSpatialParity : M2R ≃ₐ[ℝ] M2R where
  toFun A := !![A 1 1, -A 1 0; -A 0 1, A 0 0]
  invFun A := !![A 1 1, -A 1 0; -A 0 1, A 0 0]
  left_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  right_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      exact add_comm _ _
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      exact add_comm _ _
  map_add' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one]

theorem hestenesSpatialParity_involutive :
    Function.Involutive hestenesSpatialParity := by
  intro A
  exact hestenesSpatialParity.left_inv A

/-- The real spatial coefficient algebra with its Hestenes-induced grading. -/
abbrev hestenesSpatialGrading : ZMod 2 → Submodule ℝ M2R :=
  InfoGeometry.Clifford.Cl11GradedTensorMorita.involutionGrading
    hestenesSpatialParity hestenesSpatialParity_involutive

instance hestenesSpatialGradedAlgebra : GradedAlgebra hestenesSpatialGrading :=
  InfoGeometry.Clifford.Cl11GradedTensorMorita.instGradedAlgebraInvolutionGrading
    hestenesSpatialParity hestenesSpatialParity_involutive

/-- A first odd spatial generator in the real coefficient factor. -/
def hestenesSpatialX : M2R := !![0, 1; 1, 0]

/-- A second odd spatial generator in the real coefficient factor. -/
def hestenesSpatialZ : M2R := !![1, 0; 0, -1]

theorem hestenesSpatialX_odd : hestenesSpatialX ∈ hestenesSpatialGrading 1 := by
  change hestenesSpatialParity hestenesSpatialX = -hestenesSpatialX
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hestenesSpatialParity, hestenesSpatialX]

theorem hestenesSpatialZ_odd : hestenesSpatialZ ∈ hestenesSpatialGrading 1 := by
  change hestenesSpatialParity hestenesSpatialZ = -hestenesSpatialZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hestenesSpatialParity, hestenesSpatialZ]

theorem hestenesSpatialX_sq : hestenesSpatialX * hestenesSpatialX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hestenesSpatialX, Matrix.mul_apply, Fin.sum_univ_two]

theorem hestenesSpatialZ_sq : hestenesSpatialZ * hestenesSpatialZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hestenesSpatialZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem hestenesSpatial_generators_anticommute :
    hestenesSpatialX * hestenesSpatialZ +
      hestenesSpatialZ * hestenesSpatialX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hestenesSpatialX, hestenesSpatialZ,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The signature-correct native real Koszul tensor
`Cl(1,1) ᵍ⊗ Cl(2,0)` using its two real `M₂` matrix factors. -/
abbrev realMinkowskiGradedTensor :=
  CliffordAlgebra.evenOdd InfoGeometry.Clifford.Cl11Matrix.q11 ᵍ⊗[ℝ]
    hestenesSpatialGrading

/-- The existing coefficient Morita construction represents this genuine
graded tensor on nested real `M₂` blocks, retaining the Koszul parity twist. -/
noncomputable def realMinkowskiGradedTensorMorita :
    realMinkowskiGradedTensor ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) M2R :=
  InfoGeometry.Clifford.Cl11GradedTensorMorita.tensorMatrixEquiv
    hestenesSpatialGrading hestenesSpatialParity
    (by
      intro a ha
      exact InfoGeometry.Clifford.Cl11GradedTensorMorita.involutionGrading_even
        hestenesSpatialParity hestenesSpatialParity_involutive ha)
    (by
      intro a ha
      exact InfoGeometry.Clifford.Cl11GradedTensorMorita.involutionGrading_odd
        hestenesSpatialParity hestenesSpatialParity_involutive ha)

/-! ### The Hestenes operator in the real Koszul tensor

The real complex structure remains the endomorphism `J4` on the spinor
carrier. The operator algebra is the existing native Koszul-graded product
`twoMatrixGradedTensor` of two real `M₂` factors. -/

/-- The realified Hestenes spacetime operator as an endomorphism of the
four-component real spinor carrier. -/
noncomputable def realHestenesPauliEnd
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    Module.End ℝ FourSpace :=
  Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X)

/-- Canonical preimage of the real Hestenes spacetime operator in the genuine
Koszul-graded tensor of the two real `M₂(ℝ)` factors. -/
noncomputable def realHestenesPauliInGradedTensor
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    twoMatrixGradedTensor :=
  realTwoMatrixGradedTensorOnFourSpace.symm (realHestenesPauliEnd X)

theorem realHestenesPauliInGradedTensor_representation
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realTwoMatrixGradedTensorOnFourSpace (realHestenesPauliInGradedTensor X) =
      realHestenesPauliEnd X := by
  exact realTwoMatrixGradedTensorOnFourSpace.apply_symm_apply _

/-- Real spinor action of the Hestenes Hermitian Pauli representative on the
repository's four-dimensional Euclidean carrier. -/
def hestenesMinkowskiSpinorAction
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    Module.End ℝ FourSpace :=
  Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X)

/-- The `(+---)` characteristic identity remains true for the actual real
spinor endomorphism, after transporting the matrix owner through its basis. -/
theorem hestenesMinkowskiSpinorAction_cayleyHamilton
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let A := hestenesMinkowskiSpinorAction X
    A * A - (2 * X.t) • A +
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X • 1 = 0 := by
  dsimp [hestenesMinkowskiSpinorAction]
  let L := Matrix.toLinAlgEquiv
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
  have h := congrArg L (realHermitianPauli_cayleyHamilton X)
  simpa only [map_sub, map_mul, map_smul, map_add, map_zero, map_one] using h

/-- Componentwise diagonal action of a real spinor endomorphism on the two
Hestenes–Krein sheets. -/
def diagonalDoubledSpinorAction (T : Module.End ℝ FourSpace) :
    Module.End ℝ InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4 where
  toFun u := InfoGeometry.Krein.to_doubled (T (WithLp.fst u)) (T (WithLp.snd u))
  map_add' u v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp
  map_smul' c u := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp

/-- The doubled Hestenes–Krein action retains its Minkowski characteristic
identity on both sheets. -/
theorem diagonalDoubledSpinorAction_cayleyHamilton
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let A := diagonalDoubledSpinorAction (hestenesMinkowskiSpinorAction X)
    A * A - (2 * X.t) • A +
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X • 1 = 0 := by
  dsimp
  let T := hestenesMinkowskiSpinorAction X
  have h := hestenesMinkowskiSpinorAction_cayleyHamilton X
  apply LinearMap.ext
  intro u
  have hf := congrArg (fun S : Module.End ℝ FourSpace => S (WithLp.fst u)) h
  have hs := congrArg (fun S : Module.End ℝ FourSpace => S (WithLp.snd u)) h
  apply InfoGeometry.Krein.DoubledSpace.ext
  · simpa [diagonalDoubledSpinorAction, T] using hf
  · simpa [diagonalDoubledSpinorAction, T] using hs

/-- The same Hestenes momentum operator, transported through the existing
three-factor real graded `M₂` representation of the doubled Krein carrier,
retains its physical characteristic polynomial. This places the spacetime
operator in the actual real CAR representation algebra. -/
theorem realThreeGradedTensor_minkowski_cayleyHamilton
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let ρ := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorOnH4
    let A := ρ.symm (diagonalDoubledSpinorAction (hestenesMinkowskiSpinorAction X))
    A * A - (2 * X.t) • A +
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X • 1 = 0 := by
  dsimp only
  apply InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorOnH4.injective
  simp only [map_sub, map_mul, map_smul, map_add, map_zero, map_one,
    AlgEquiv.apply_symm_apply]
  exact diagonalDoubledSpinorAction_cayleyHamilton X

/-! ### A real `Cl(1,1)` pair inside the first graded CAR factor

The first real `M₂` factor is not merely a carrier with a CAR relation. Its
annihilation and creation units give a concrete split-Clifford pair. This is
the first pair in the eventual real spacetime Clifford action; additional
spatial generators must use the other Koszul-graded factors. -/

/-- The first Majorana combination is the positive-square generator. -/
def realMajoranaTimeHead :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixGradedTensor :=
  InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationHead +
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationHead

/-- The complementary real Majorana combination is the negative-square
generator in the same first `M₂(ℝ)` factor. -/
def realMajoranaSpaceHead :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixGradedTensor :=
  InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationHead -
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationHead

private theorem realThreeAnnihilationHead_sq :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationHead ^ 2 = 0 := by
  apply InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita.injective
  rw [map_pow, InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita_annihilationHead]
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, Matrix.mul_apply]

private theorem realThreeCreationHead_sq :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationHead ^ 2 = 0 := by
  apply InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita.injective
  rw [map_pow, InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita_creationHead]
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, Matrix.mul_apply]

/-- The owner CAR mode yields two anticommuting real Clifford generators
with exact signs `(+,−)` inside the native three-factor graded tensor. -/
theorem realMajoranaHead_splitClifford_relations :
    realMajoranaTimeHead * realMajoranaTimeHead = 1 ∧
    realMajoranaSpaceHead * realMajoranaSpaceHead = -1 ∧
    realMajoranaTimeHead * realMajoranaSpaceHead +
      realMajoranaSpaceHead * realMajoranaTimeHead = 0 := by
  have hA2 := realThreeAnnihilationHead_sq
  have hC2 := realThreeCreationHead_sq
  have hCAR :=
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensor_head_CAR
  have hA2' :
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationHead *
        InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationHead = 0 := by
    simpa only [pow_two] using hA2
  have hC2' :
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationHead *
        InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationHead = 0 := by
    simpa only [pow_two] using hC2
  let a := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationHead
  let c := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationHead
  have ha2 : a * a = 0 := hA2'
  have hc2 : c * c = 0 := hC2'
  have hac : a * c + c * a = 1 := hCAR
  constructor
  · change (a + c) * (a + c) = 1
    calc
      (a + c) * (a + c) = a * a + (a * c + c * a) + c * c := by noncomm_ring
      _ = 1 := by rw [ha2, hac, hc2]; simp
  constructor
  · change (a - c) * (a - c) = -1
    calc
      (a - c) * (a - c) = a * a - (a * c + c * a) + c * c := by noncomm_ring
      _ = -1 := by rw [ha2, hac, hc2]; simp
  · change (a + c) * (a - c) + (a - c) * (a + c) = 0
    calc
      (a + c) * (a - c) + (a - c) * (a + c) =
          a * a - c * c + (a * a - c * c) := by noncomm_ring
      _ = 0 := by rw [ha2, hc2]; simp

/-! ### The remaining two real CAR modes and a `Cl(1,3)` frame

The graded tensor has three independent real CAR modes. Each produces a
`Cl(1,1)` pair; choosing the positive generator of the first mode and the
negative generator of each mode gives a concrete `Cl(1,3)` frame. -/

/-- The positive Majorana combination in the second real CAR mode. -/
def realMajoranaTimeMiddle :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixGradedTensor :=
  InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationMiddle +
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationMiddle

/-- The negative Majorana combination in the second real CAR mode. -/
def realMajoranaSpaceMiddle :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixGradedTensor :=
  InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationMiddle -
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationMiddle

/-- The positive Majorana combination in the third real CAR mode. -/
def realMajoranaTimeTail :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixGradedTensor :=
  InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationTail +
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationTail

/-- The negative Majorana combination in the third real CAR mode. -/
def realMajoranaSpaceTail :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixGradedTensor :=
  InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationTail -
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationTail

private theorem realThreeMiddle_annihilation_sq :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationMiddle ^ 2 = 0 := by
  apply InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita.injective
  rw [map_pow, map_zero]
  simp only [InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationMiddle,
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita_tail]
  rw [pow_two]
  have h := InfoGeometry.Canonical.GradedTensorWeylBridge.annihilation₀_sq
  have hp : InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
      InfoGeometry.Canonical.GradedTensorWeylBridge.annihilation₀ *
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
        InfoGeometry.Canonical.GradedTensorWeylBridge.annihilation₀ = 0 := by
    simpa only [map_mul, map_zero] using congrArg
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity h
  ext i j
  apply InfoGeometry.Canonical.SplitCliffordTowerUnification.twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, hp]

private theorem realThreeMiddle_creation_sq :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationMiddle ^ 2 = 0 := by
  apply InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita.injective
  rw [map_pow, map_zero]
  simp only [InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationMiddle,
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita_tail]
  rw [pow_two]
  have hE : InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10 *
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10,
        Matrix.single, Matrix.mul_apply]
  have h : InfoGeometry.Canonical.GradedTensorWeylBridge.creation₀ *
      InfoGeometry.Canonical.GradedTensorWeylBridge.creation₀ = 0 := by
    change (InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10 ᵍ⊗ₜ[ℝ]
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10 ᵍ⊗ₜ[ℝ]
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
    rw [GradedTensorProduct.tmul_coe_mul_coe_tmul
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10
      (⟨(1 : Matrix (Fin 2) (Fin 2) ℝ),
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixOne_even⟩ :
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading 0)
      (⟨InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10,
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10_odd⟩ :
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading 1)
      (1 : Matrix (Fin 2) (Fin 2) ℝ)]
    simp [hE]
  have hp : InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
      InfoGeometry.Canonical.GradedTensorWeylBridge.creation₀ *
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
        InfoGeometry.Canonical.GradedTensorWeylBridge.creation₀ = 0 := by
    simpa only [map_mul, map_zero] using congrArg
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity h
  ext i j
  apply InfoGeometry.Canonical.SplitCliffordTowerUnification.twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, hp]

private theorem realThreeTail_annihilation_sq :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationTail ^ 2 = 0 := by
  apply InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita.injective
  rw [map_pow, map_zero]
  simp only [InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationTail,
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita_tail]
  rw [pow_two]
  have h := InfoGeometry.Canonical.GradedTensorWeylBridge.annihilation₁_sq
  have hp : InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
      InfoGeometry.Canonical.GradedTensorWeylBridge.annihilation₁ *
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
        InfoGeometry.Canonical.GradedTensorWeylBridge.annihilation₁ = 0 := by
    simpa only [map_mul, map_zero] using congrArg
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity h
  ext i j
  apply InfoGeometry.Canonical.SplitCliffordTowerUnification.twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, hp]

private theorem realThreeTail_creation_sq :
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationTail ^ 2 = 0 := by
  apply InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita.injective
  rw [map_pow, map_zero]
  simp only [InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationTail,
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensorMorita_tail]
  rw [pow_two]
  have hE : InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10 *
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10,
        Matrix.single, Matrix.mul_apply]
  have h : InfoGeometry.Canonical.GradedTensorWeylBridge.creation₁ *
      InfoGeometry.Canonical.GradedTensorWeylBridge.creation₁ = 0 := by
    change ((1 : Matrix (Fin 2) (Fin 2) ℝ) ᵍ⊗ₜ[ℝ]
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10) *
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) ᵍ⊗ₜ[ℝ]
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10) = 0
    rw [GradedTensorProduct.tmul_coe_mul_coe_tmul
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading
      (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (⟨InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10,
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10_odd⟩ :
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading 1)
      (⟨(1 : Matrix (Fin 2) (Fin 2) ℝ),
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixOne_even⟩ :
        InfoGeometry.Canonical.GradedTensorWeylBridge.matrixGrading 0)
      InfoGeometry.Canonical.GradedTensorWeylBridge.matrixE10]
    simp [hE]
  have hp : InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
      InfoGeometry.Canonical.GradedTensorWeylBridge.creation₁ *
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity
        InfoGeometry.Canonical.GradedTensorWeylBridge.creation₁ = 0 := by
    simpa only [map_mul, map_zero] using congrArg
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoMatrixParity h
  ext i j
  apply InfoGeometry.Canonical.SplitCliffordTowerUnification.twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, hp]

/-- Each of the second and third actual CAR modes supplies a split-Clifford
pair with exact squares `(+,−)` and zero mixed anticommutator. -/
theorem realMajoranaMiddle_splitClifford_relations :
    realMajoranaTimeMiddle * realMajoranaTimeMiddle = 1 ∧
    realMajoranaSpaceMiddle * realMajoranaSpaceMiddle = -1 ∧
    realMajoranaTimeMiddle * realMajoranaSpaceMiddle +
      realMajoranaSpaceMiddle * realMajoranaTimeMiddle = 0 := by
  have hA2 := realThreeMiddle_annihilation_sq
  have hC2 := realThreeMiddle_creation_sq
  have hCAR := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensor_middle_CAR
  have hA2' := hA2
  have hC2' := hC2
  rw [pow_two] at hA2' hC2'
  let a := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationMiddle
  let c := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationMiddle
  have ha2 : a * a = 0 := hA2'
  have hc2 : c * c = 0 := hC2'
  have hac : a * c + c * a = 1 := hCAR
  constructor
  · change (a + c) * (a + c) = 1
    calc (a + c) * (a + c) = a * a + (a * c + c * a) + c * c := by noncomm_ring
      _ = 1 := by rw [ha2, hac, hc2]; simp
  constructor
  · change (a - c) * (a - c) = -1
    calc (a - c) * (a - c) = a * a - (a * c + c * a) + c * c := by noncomm_ring
      _ = -1 := by rw [ha2, hac, hc2]; simp
  · change (a + c) * (a - c) + (a - c) * (a + c) = 0
    calc (a + c) * (a - c) + (a - c) * (a + c) =
        a * a - c * c + (a * a - c * c) := by noncomm_ring
      _ = 0 := by rw [ha2, hc2]; simp

/-- The third actual CAR mode gives the same real split-Clifford pair. -/
theorem realMajoranaTail_splitClifford_relations :
    realMajoranaTimeTail * realMajoranaTimeTail = 1 ∧
    realMajoranaSpaceTail * realMajoranaSpaceTail = -1 ∧
    realMajoranaTimeTail * realMajoranaSpaceTail +
      realMajoranaSpaceTail * realMajoranaTimeTail = 0 := by
  have hA2 := realThreeTail_annihilation_sq
  have hC2 := realThreeTail_creation_sq
  have hCAR := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixTensor_tail_CAR
  rw [pow_two] at hA2 hC2
  let a := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeAnnihilationTail
  let c := InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeCreationTail
  have ha2 : a * a = 0 := hA2
  have hc2 : c * c = 0 := hC2
  have hac : a * c + c * a = 1 := hCAR
  constructor
  · change (a + c) * (a + c) = 1
    calc (a + c) * (a + c) = a * a + (a * c + c * a) + c * c := by noncomm_ring
      _ = 1 := by rw [ha2, hac, hc2]; simp
  constructor
  · change (a - c) * (a - c) = -1
    calc (a - c) * (a - c) = a * a - (a * c + c * a) + c * c := by noncomm_ring
      _ = -1 := by rw [ha2, hac, hc2]; simp
  · change (a + c) * (a - c) + (a - c) * (a + c) = 0
    calc (a + c) * (a - c) + (a - c) * (a + c) =
        a * a - c * c + (a * a - c * c) := by noncomm_ring
      _ = 0 := by rw [ha2, hc2]; simp

/-- The four selected real Majorana generators have the diagonal square
pattern `(+,−,−,−)`. This records the diagonal part of the prospective
spacetime Clifford relations; it does not alone assert pairwise
anticommutation. -/
theorem realMajorana_minkowski_diagonal_squares :
    realMajoranaTimeHead * realMajoranaTimeHead = 1 ∧
    realMajoranaSpaceHead * realMajoranaSpaceHead = -1 ∧
    realMajoranaSpaceMiddle * realMajoranaSpaceMiddle = -1 ∧
    realMajoranaSpaceTail * realMajoranaSpaceTail = -1 := by
  exact ⟨realMajoranaHead_splitClifford_relations.1,
    realMajoranaHead_splitClifford_relations.2.1,
    realMajoranaMiddle_splitClifford_relations.2.1,
    realMajoranaTail_splitClifford_relations.2.1⟩

/-- The negative Majorana operators from the second and third real CAR modes
anticommute; this uses the existing Koszul signs in the two-factor owner and
the parity-twisted lower block of the three-factor Morita map. -/
theorem realMajoranaSpaceMiddle_spaceTail_anticommute :
    realMajoranaSpaceMiddle * realMajoranaSpaceTail +
      realMajoranaSpaceTail * realMajoranaSpaceMiddle = 0 := by
  have haa := annihilation₀_annihilation₁_anticommute
  have hac := annihilation₀_creation₁_anticommute
  have hca := annihilation₁_creation₀_anticommute
  have hca' : creation₀ * annihilation₁ + annihilation₁ * creation₀ = 0 := by
    simpa only [add_comm] using hca
  have hcc := creation₀_creation₁_anticommute
  have hlocal :
      (annihilation₀ - creation₀) * (annihilation₁ - creation₁) +
        (annihilation₁ - creation₁) * (annihilation₀ - creation₀) = 0 := by
    calc
      _ = (annihilation₀ * annihilation₁ + annihilation₁ * annihilation₀) -
          (annihilation₀ * creation₁ + creation₁ * annihilation₀) -
          (creation₀ * annihilation₁ + annihilation₁ * creation₀) +
          (creation₀ * creation₁ + creation₁ * creation₀) := by noncomm_ring
      _ = 0 := by rw [haa, hac, hca', hcc]; simp
  have hpar := congrArg twoMatrixParity hlocal
  have hpar' : twoMatrixParity (annihilation₀ - creation₀) *
      twoMatrixParity (annihilation₁ - creation₁) +
    twoMatrixParity (annihilation₁ - creation₁) *
      twoMatrixParity (annihilation₀ - creation₀) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using hpar
  have hlocalMap :
      twoMatrixGradedTensorMoritaEquiv (annihilation₀ - creation₀) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₁ - creation₁) +
        twoMatrixGradedTensorMoritaEquiv (annihilation₁ - creation₁) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₀ - creation₀) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hlocal
  have hparMap :
      twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ - creation₀)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ - creation₁)) +
        twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ - creation₁)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ - creation₀)) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hpar'
  apply realThreeMatrixTensorMorita.injective
  simp only [realMajoranaSpaceMiddle, realMajoranaSpaceTail,
    map_add, map_sub, map_mul, map_zero,
    realThreeAnnihilationMiddle, realThreeCreationMiddle,
    realThreeAnnihilationTail, realThreeCreationTail,
    realThreeMatrixTensorMorita_tail]
  ext i j
  apply twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hlocalMap
  · simp
  · simp
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hparMap

private theorem twoMatrixMajoranaSpace_odd :
    twoMatrixParity (annihilation₀ - creation₀) =
      -(annihilation₀ - creation₀) := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [twoMatrixParity_apply]
  simp only [map_sub, map_neg, annihilation₀, creation₀,
    twoMatrixGradedTensorMoritaEquiv_tmul]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [GradedTensorWeylBridge.matrixE01,
      GradedTensorWeylBridge.matrixE10, matrixGrade_apply,
      matrixParity_apply, Matrix.single]

private theorem twoMatrixMajoranaTime_odd :
    twoMatrixParity (annihilation₀ + creation₀) =
      -(annihilation₀ + creation₀) := by
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [twoMatrixParity_apply]
  simp only [map_add, map_neg, annihilation₀, creation₀,
    twoMatrixGradedTensorMoritaEquiv_tmul]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [GradedTensorWeylBridge.matrixE01,
      GradedTensorWeylBridge.matrixE10, matrixGrade_apply,
      matrixParity_apply, Matrix.single]

private theorem realMajoranaTimeHead_representation :
    realThreeMatrixTensorMorita realMajoranaTimeHead = !![0, 1; 1, 0] := by
  change realThreeMatrixTensorMorita
    (realThreeAnnihilationHead + realThreeCreationHead) = _
  rw [map_add, realThreeMatrixTensorMorita_annihilationHead,
    realThreeMatrixTensorMorita_creationHead]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

private theorem realMajoranaTimeMiddle_representation :
    realThreeMatrixTensorMorita realMajoranaTimeMiddle =
      !![annihilation₀ + creation₀, 0; 0, -(annihilation₀ + creation₀)] := by
  change realThreeMatrixTensorMorita
    (realThreeAnnihilationMiddle + realThreeCreationMiddle) = _
  rw [map_add]
  dsimp only [realThreeAnnihilationMiddle, realThreeCreationMiddle]
  rw [realThreeMatrixTensorMorita_tail, realThreeMatrixTensorMorita_tail]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simp
  · calc
      twoMatrixParity annihilation₀ + twoMatrixParity creation₀ =
          twoMatrixParity (annihilation₀ + creation₀) := (map_add _ _ _).symm
      _ = -(annihilation₀ + creation₀) := twoMatrixMajoranaTime_odd
      _ = (!![annihilation₀ + creation₀, 0;
        0, -(annihilation₀ + creation₀)] : Matrix (Fin 2) (Fin 2)
        twoMatrixGradedTensor) 1 1 := by rfl

/-- The time Majoranas in the first and second real CAR modes anticommute
after the genuine graded-Morita representation. The sign comes from the
odd parity of the second-mode coefficient, not from an ungraded Kronecker
product. -/
theorem realMajoranaTimeHead_timeMiddle_anticommute :
    realMajoranaTimeHead * realMajoranaTimeMiddle +
      realMajoranaTimeMiddle * realMajoranaTimeHead = 0 := by
  apply realThreeMatrixTensorMorita.injective
  rw [map_add, map_mul, map_mul, map_zero,
    realMajoranaTimeHead_representation,
    realMajoranaTimeMiddle_representation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp

private theorem realMajoranaSpaceHead_representation :
    realThreeMatrixTensorMorita realMajoranaSpaceHead = !![0, 1; -1, 0] := by
  change realThreeMatrixTensorMorita
    (realThreeAnnihilationHead - realThreeCreationHead) = _
  rw [map_sub, realThreeMatrixTensorMorita_annihilationHead,
    realThreeMatrixTensorMorita_creationHead]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

private theorem realMajoranaSpaceMiddle_representation :
    realThreeMatrixTensorMorita realMajoranaSpaceMiddle =
      !![annihilation₀ - creation₀, 0; 0, -(annihilation₀ - creation₀)] := by
  change realThreeMatrixTensorMorita
    (realThreeAnnihilationMiddle - realThreeCreationMiddle) = _
  rw [map_sub]
  dsimp only [realThreeAnnihilationMiddle, realThreeCreationMiddle]
  rw [realThreeMatrixTensorMorita_tail, realThreeMatrixTensorMorita_tail]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simp
  · calc
      twoMatrixParity annihilation₀ - twoMatrixParity creation₀ =
          twoMatrixParity (annihilation₀ - creation₀) := (map_sub _ _ _).symm
      _ = -(annihilation₀ - creation₀) := twoMatrixMajoranaSpace_odd
      _ = (!![annihilation₀ - creation₀, 0;
        0, -(annihilation₀ - creation₀)] : Matrix (Fin 2) (Fin 2)
        twoMatrixGradedTensor) 1 1 := by rfl

private theorem twoMatrixMajoranaTimeTailCoefficient_odd :
    twoMatrixParity (annihilation₁ + creation₁) =
      -(annihilation₁ + creation₁) := by
  have hA := twoMatrixGradedTensorMoritaEquiv_annihilation₁
  have hC := twoMatrixGradedTensorMoritaEquiv_creation₁
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [twoMatrixParity_apply]
  simp only [map_add, map_neg, hA, hC]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [matrixGrade_apply, matrixParity_apply,
      GradedTensorWeylBridge.matrixE01, GradedTensorWeylBridge.matrixE10,
      Matrix.single]

private theorem twoMatrixMajoranaSpaceTailCoefficient_odd :
    twoMatrixParity (annihilation₁ - creation₁) =
      -(annihilation₁ - creation₁) := by
  have hA := twoMatrixGradedTensorMoritaEquiv_annihilation₁
  have hC := twoMatrixGradedTensorMoritaEquiv_creation₁
  apply twoMatrixGradedTensorMoritaEquiv.injective
  rw [twoMatrixParity_apply]
  simp only [map_sub, map_neg, hA, hC]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [matrixGrade_apply, matrixParity_apply,
      GradedTensorWeylBridge.matrixE01, GradedTensorWeylBridge.matrixE10,
      Matrix.single]

private theorem realMajoranaTimeTail_representation :
    realThreeMatrixTensorMorita realMajoranaTimeTail =
      !![annihilation₁ + creation₁, 0; 0, -(annihilation₁ + creation₁)] := by
  change realThreeMatrixTensorMorita
    (realThreeAnnihilationTail + realThreeCreationTail) = _
  rw [map_add]
  dsimp only [realThreeAnnihilationTail, realThreeCreationTail]
  rw [realThreeMatrixTensorMorita_tail, realThreeMatrixTensorMorita_tail]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simp
  · calc
      twoMatrixParity annihilation₁ + twoMatrixParity creation₁ =
          twoMatrixParity (annihilation₁ + creation₁) := (map_add _ _ _).symm
      _ = -(annihilation₁ + creation₁) := twoMatrixMajoranaTimeTailCoefficient_odd
      _ = (!![annihilation₁ + creation₁, 0;
        0, -(annihilation₁ + creation₁)] : Matrix (Fin 2) (Fin 2)
        twoMatrixGradedTensor) 1 1 := by rfl

private theorem realMajoranaSpaceTail_representation :
    realThreeMatrixTensorMorita realMajoranaSpaceTail =
      !![annihilation₁ - creation₁, 0; 0, -(annihilation₁ - creation₁)] := by
  change realThreeMatrixTensorMorita
    (realThreeAnnihilationTail - realThreeCreationTail) = _
  rw [map_sub]
  dsimp only [realThreeAnnihilationTail, realThreeCreationTail]
  rw [realThreeMatrixTensorMorita_tail, realThreeMatrixTensorMorita_tail]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simp
  · calc
      twoMatrixParity annihilation₁ - twoMatrixParity creation₁ =
          twoMatrixParity (annihilation₁ - creation₁) := (map_sub _ _ _).symm
      _ = -(annihilation₁ - creation₁) := twoMatrixMajoranaSpaceTailCoefficient_odd
      _ = (!![annihilation₁ - creation₁, 0;
        0, -(annihilation₁ - creation₁)] : Matrix (Fin 2) (Fin 2)
        twoMatrixGradedTensor) 1 1 := by rfl

/-- All four mixed anticommutators between the first real Majorana mode and
the third mode vanish in the native three-factor Koszul tensor. This closes
the first-to-third CAR lane using the existing graded Morita action. -/
theorem realMajoranaHead_tail_cross_anticommutators :
    realMajoranaTimeHead * realMajoranaTimeTail +
        realMajoranaTimeTail * realMajoranaTimeHead = 0 ∧
    realMajoranaTimeHead * realMajoranaSpaceTail +
        realMajoranaSpaceTail * realMajoranaTimeHead = 0 ∧
    realMajoranaSpaceHead * realMajoranaTimeTail +
        realMajoranaTimeTail * realMajoranaSpaceHead = 0 ∧
    realMajoranaSpaceHead * realMajoranaSpaceTail +
        realMajoranaSpaceTail * realMajoranaSpaceHead = 0 := by
  constructor
  · apply realThreeMatrixTensorMorita.injective
    rw [map_add, map_mul, map_mul, map_zero,
      realMajoranaTimeHead_representation, realMajoranaTimeTail_representation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · apply realThreeMatrixTensorMorita.injective
    rw [map_add, map_mul, map_mul, map_zero,
      realMajoranaTimeHead_representation, realMajoranaSpaceTail_representation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · apply realThreeMatrixTensorMorita.injective
    rw [map_add, map_mul, map_mul, map_zero,
      realMajoranaSpaceHead_representation, realMajoranaTimeTail_representation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · apply realThreeMatrixTensorMorita.injective
    rw [map_add, map_mul, map_mul, map_zero,
      realMajoranaSpaceHead_representation, realMajoranaSpaceTail_representation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- All four cross anticommutators between the first and second real CAR
modes vanish. This is the full pairwise Koszul relation table for those two
modes, transported by the existing faithful graded Morita representation. -/
theorem realMajoranaHead_middle_cross_anticommutators :
    realMajoranaTimeHead * realMajoranaSpaceMiddle +
        realMajoranaSpaceMiddle * realMajoranaTimeHead = 0 ∧
    realMajoranaSpaceHead * realMajoranaTimeMiddle +
        realMajoranaTimeMiddle * realMajoranaSpaceHead = 0 ∧
    realMajoranaSpaceHead * realMajoranaSpaceMiddle +
        realMajoranaSpaceMiddle * realMajoranaSpaceHead = 0 := by
  constructor
  · apply realThreeMatrixTensorMorita.injective
    rw [map_add, map_mul, map_mul, map_zero,
      realMajoranaTimeHead_representation,
      realMajoranaSpaceMiddle_representation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · apply realThreeMatrixTensorMorita.injective
    rw [map_add, map_mul, map_mul, map_zero,
      realMajoranaSpaceHead_representation,
      realMajoranaTimeMiddle_representation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · apply realThreeMatrixTensorMorita.injective
    rw [map_add, map_mul, map_mul, map_zero,
      realMajoranaSpaceHead_representation,
      realMajoranaSpaceMiddle_representation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The time Majoranas from the second and third real CAR modes anticommute.
This transports the native two-factor Koszul CAR identity through the
parity-twisted lower block of the existing three-factor Morita map. -/
theorem realMajoranaTimeMiddle_timeTail_anticommute :
    realMajoranaTimeMiddle * realMajoranaTimeTail +
      realMajoranaTimeTail * realMajoranaTimeMiddle = 0 := by
  have haa := annihilation₀_annihilation₁_anticommute
  have hac := annihilation₀_creation₁_anticommute
  have hca := annihilation₁_creation₀_anticommute
  have hca' : creation₀ * annihilation₁ + annihilation₁ * creation₀ = 0 := by
    simpa only [add_comm] using hca
  have hcc := creation₀_creation₁_anticommute
  have hlocal :
      (annihilation₀ + creation₀) * (annihilation₁ + creation₁) +
        (annihilation₁ + creation₁) * (annihilation₀ + creation₀) = 0 := by
    calc
      _ = (annihilation₀ * annihilation₁ + annihilation₁ * annihilation₀) +
          (annihilation₀ * creation₁ + creation₁ * annihilation₀) +
          (creation₀ * annihilation₁ + annihilation₁ * creation₀) +
          (creation₀ * creation₁ + creation₁ * creation₀) := by noncomm_ring
      _ = 0 := by rw [haa, hac, hca', hcc]; simp
  have hpar := congrArg twoMatrixParity hlocal
  have hpar' : twoMatrixParity (annihilation₀ + creation₀) *
      twoMatrixParity (annihilation₁ + creation₁) +
    twoMatrixParity (annihilation₁ + creation₁) *
      twoMatrixParity (annihilation₀ + creation₀) = 0 := by
    simpa only [map_add, map_mul, map_zero] using hpar
  have hlocalMap :
      twoMatrixGradedTensorMoritaEquiv (annihilation₀ + creation₀) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₁ + creation₁) +
        twoMatrixGradedTensorMoritaEquiv (annihilation₁ + creation₁) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₀ + creation₀) = 0 := by
    simpa only [map_add, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hlocal
  have hparMap :
      twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ + creation₀)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ + creation₁)) +
        twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ + creation₁)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ + creation₀)) = 0 := by
    simpa only [map_add, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hpar'
  apply realThreeMatrixTensorMorita.injective
  simp only [realMajoranaTimeMiddle, realMajoranaTimeTail,
    map_add, map_mul, map_zero,
    realThreeAnnihilationMiddle, realThreeCreationMiddle,
    realThreeAnnihilationTail, realThreeCreationTail,
    realThreeMatrixTensorMorita_tail]
  ext i j
  apply twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hlocalMap
  · simp
  · simp
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hparMap

/-- The time Majorana in the middle mode anticommutes with the space
Majorana in the tail mode, with the sign supplied by the native two-factor
CAR cross-relations. -/
theorem realMajoranaTimeMiddle_spaceTail_anticommute :
    realMajoranaTimeMiddle * realMajoranaSpaceTail +
      realMajoranaSpaceTail * realMajoranaTimeMiddle = 0 := by
  have haa := annihilation₀_annihilation₁_anticommute
  have hac := annihilation₀_creation₁_anticommute
  have hca := annihilation₁_creation₀_anticommute
  have hca' : creation₀ * annihilation₁ + annihilation₁ * creation₀ = 0 := by
    simpa only [add_comm] using hca
  have hcc := creation₀_creation₁_anticommute
  have hlocal :
      (annihilation₀ + creation₀) * (annihilation₁ - creation₁) +
        (annihilation₁ - creation₁) * (annihilation₀ + creation₀) = 0 := by
    calc
      _ = (annihilation₀ * annihilation₁ + annihilation₁ * annihilation₀) +
          (creation₀ * annihilation₁ + annihilation₁ * creation₀) -
          (annihilation₀ * creation₁ + creation₁ * annihilation₀) -
          (creation₀ * creation₁ + creation₁ * creation₀) := by noncomm_ring
      _ = 0 := by rw [haa, hca', hac, hcc]; simp
  have hpar := congrArg twoMatrixParity hlocal
  have hpar' : twoMatrixParity (annihilation₀ + creation₀) *
      twoMatrixParity (annihilation₁ - creation₁) +
    twoMatrixParity (annihilation₁ - creation₁) *
      twoMatrixParity (annihilation₀ + creation₀) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using hpar
  have hlocalMap :
      twoMatrixGradedTensorMoritaEquiv (annihilation₀ + creation₀) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₁ - creation₁) +
        twoMatrixGradedTensorMoritaEquiv (annihilation₁ - creation₁) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₀ + creation₀) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hlocal
  have hparMap :
      twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ + creation₀)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ - creation₁)) +
        twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ - creation₁)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ + creation₀)) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hpar'
  apply realThreeMatrixTensorMorita.injective
  simp only [realMajoranaTimeMiddle, realMajoranaSpaceTail,
    map_add, map_sub, map_mul, map_zero,
    realThreeAnnihilationMiddle, realThreeCreationMiddle,
    realThreeAnnihilationTail, realThreeCreationTail,
    realThreeMatrixTensorMorita_tail]
  ext i j
  apply twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hlocalMap
  · simp
  · simp
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hparMap

/-- The space Majorana in the middle mode anticommutes with the time
Majorana in the tail mode. -/
theorem realMajoranaSpaceMiddle_timeTail_anticommute :
    realMajoranaSpaceMiddle * realMajoranaTimeTail +
      realMajoranaTimeTail * realMajoranaSpaceMiddle = 0 := by
  have haa := annihilation₀_annihilation₁_anticommute
  have hac := annihilation₀_creation₁_anticommute
  have hca := annihilation₁_creation₀_anticommute
  have hca' : creation₀ * annihilation₁ + annihilation₁ * creation₀ = 0 := by
    simpa only [add_comm] using hca
  have hcc := creation₀_creation₁_anticommute
  have hlocal :
      (annihilation₀ - creation₀) * (annihilation₁ + creation₁) +
        (annihilation₁ + creation₁) * (annihilation₀ - creation₀) = 0 := by
    calc
      _ = (annihilation₀ * annihilation₁ + annihilation₁ * annihilation₀) +
          (annihilation₀ * creation₁ + creation₁ * annihilation₀) -
          (creation₀ * annihilation₁ + annihilation₁ * creation₀) -
          (creation₀ * creation₁ + creation₁ * creation₀) := by noncomm_ring
      _ = 0 := by rw [haa, hac, hca', hcc]; simp
  have hpar := congrArg twoMatrixParity hlocal
  have hpar' : twoMatrixParity (annihilation₀ - creation₀) *
      twoMatrixParity (annihilation₁ + creation₁) +
    twoMatrixParity (annihilation₁ + creation₁) *
      twoMatrixParity (annihilation₀ - creation₀) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using hpar
  have hlocalMap :
      twoMatrixGradedTensorMoritaEquiv (annihilation₀ - creation₀) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₁ + creation₁) +
        twoMatrixGradedTensorMoritaEquiv (annihilation₁ + creation₁) *
          twoMatrixGradedTensorMoritaEquiv (annihilation₀ - creation₀) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hlocal
  have hparMap :
      twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ - creation₀)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ + creation₁)) +
        twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₁ + creation₁)) *
          twoMatrixGradedTensorMoritaEquiv (twoMatrixParity (annihilation₀ - creation₀)) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_zero] using
      congrArg twoMatrixGradedTensorMoritaEquiv hpar'
  apply realThreeMatrixTensorMorita.injective
  simp only [realMajoranaSpaceMiddle, realMajoranaTimeTail,
    map_add, map_sub, map_mul, map_zero,
    realThreeAnnihilationMiddle, realThreeCreationMiddle,
    realThreeAnnihilationTail, realThreeCreationTail,
    realThreeMatrixTensorMorita_tail]
  ext i j
  apply twoMatrixGradedTensorMoritaEquiv.injective
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hlocalMap
  · simp
  · simp
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hparMap
end InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
