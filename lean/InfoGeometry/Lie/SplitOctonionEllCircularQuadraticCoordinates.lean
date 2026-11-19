/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionErlangenInvariant
import InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge

/-!
# The native determinant in circular Peirce coordinates

The circular coordinates carry the native Zorn determinant by a genuine
`QuadraticForm.comp` transport.  No coordinate polynomial or associativity
claim is imposed; the transported form is definitionally the determinant of
the canonical alternative carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates

open InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionErlangenInvariant
open InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Canonical.ZornMatrix

abbrev CanonicalZorn :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

noncomputable def circularPeirceQuadratic :
    QuadraticForm ℝ (Fin 8 → ℝ) :=
  canonicalDetQuadratic.comp circularPeirceBasis.equivFun.symm

theorem circularPeirceQuadratic_apply_coord (x : Fin 8 → ℝ) :
    circularPeirceQuadratic x =
      canonicalDetQuadratic (circularPeirceBasis.equivFun.symm x) := by
  rfl

set_option maxHeartbeats 1000000
theorem circularPeirceQuadratic_formula (x : Fin 8 → ℝ) :
    circularPeirceQuadratic x =
      x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7) := by
  rw [circularPeirceQuadratic_apply_coord]
  rw [circularPeirceBasis.equivFun_symm_apply]
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
    (∑ i : Fin 8, x i • circularPeirceBasis i) = _
  rw [show (∑ i : Fin 8, x i • circularPeirceBasis i) =
      ∑ i : Fin 8, x i • frame i by
    apply Finset.sum_congr rfl
    intro i hi
    rw [circularPeirceBasis_apply]]
  have hsmul (r : ℝ) (Z : CanonicalZorn) :
      r • Z = { a := r * Z.a, b := r * Z.b, x := r • Z.x, y := r • Z.y } := by
    ext <;> rfl
  rw [Fin.sum_univ_eight]
  simp only [frame, uPlus, uMinus, rootPlus, rootMinus,
    chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
    lUnit, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    hsmul]
  simp [InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  ring

theorem circularPeirceQuadratic_zero_iff (x : Fin 8 → ℝ) :
    circularPeirceQuadratic x = 0 ↔
      x 0 * x 4 = x 1 * x 5 + x 2 * x 6 + x 3 * x 7 := by
  rw [circularPeirceQuadratic_formula]
  constructor <;> intro h <;> linarith

@[simp] theorem circularPeirceQuadratic_apply (X : CanonicalZorn) :
    circularPeirceQuadratic (coordinateEquiv X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X := by
  change canonicalDetQuadratic
      (circularPeirceBasis.equivFun.symm (coordinateEquiv X)) = _
  change canonicalDetQuadratic
      (circularPeirceBasis.equivFun.symm
        (circularPeirceBasis.equivFun X)) = _
  rw [circularPeirceBasis.equivFun.symm_apply_apply]
  simp [canonicalDetQuadratic]

/-- Transporting a real split-octonion automorphism to Ell-circular
coordinates preserves the native determinant quadratic form. This connects
the coordinate-sector action to the composition structure of the carrier. -/
theorem ellCoordinateAutomorphism_preserves_circularPeirceQuadratic
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : Fin 8 → ℝ) :
    circularPeirceQuadratic (ellCoordinateAutomorphism φ x) =
      circularPeirceQuadratic x := by
  calc
    circularPeirceQuadratic (ellCoordinateAutomorphism φ x) =
        circularPeirceQuadratic (coordinateEquiv
          ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
            (coordinateEquiv.symm x))) := rfl
    _ = InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
          ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
            (coordinateEquiv.symm x)) := circularPeirceQuadratic_apply _
    _ = InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
          (coordinateEquiv.symm x) := by
          exact InfoGeometry.Canonical.RealSplitOctonionAut.preserves_detZ φ _
    _ = circularPeirceQuadratic (coordinateEquiv (coordinateEquiv.symm x)) :=
          (circularPeirceQuadratic_apply _).symm
    _ = circularPeirceQuadratic x := by rw [coordinateEquiv.apply_symm_apply]

/-- In coordinates, determinant preservation is the preservation of the
split pairing between the positive and negative Peirce sectors. -/
theorem ellCoordinateAutomorphism_preserves_circularPeircePairing
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x : Fin 8 → ℝ) :
    (ellCoordinateAutomorphism φ x) 0 * (ellCoordinateAutomorphism φ x) 4 -
        ((ellCoordinateAutomorphism φ x) 1 * (ellCoordinateAutomorphism φ x) 5 +
          (ellCoordinateAutomorphism φ x) 2 * (ellCoordinateAutomorphism φ x) 6 +
          (ellCoordinateAutomorphism φ x) 3 * (ellCoordinateAutomorphism φ x) 7) =
      x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7) := by
  rw [← circularPeirceQuadratic_formula, ← circularPeirceQuadratic_formula,
    ellCoordinateAutomorphism_preserves_circularPeirceQuadratic]

/-- Polarization of the native split determinant in the Ell-circular basis.
It pairs the `(+1)` and `(-1)` regular-`J` sectors with signature
`(+,-,-,-)`. -/
def circularPeirceBilinearForm (x y : Fin 8 → ℝ) : ℝ :=
  x 0 * y 4 + y 0 * x 4 -
    (x 1 * y 5 + y 1 * x 5 + x 2 * y 6 + y 2 * x 6 +
      x 3 * y 7 + y 3 * x 7)

theorem circularPeirceBilinearForm_eq_quadratic_polarization
    (x y : Fin 8 → ℝ) :
    circularPeirceBilinearForm x y =
      circularPeirceQuadratic (x + y) - circularPeirceQuadratic x -
        circularPeirceQuadratic y := by
  rw [circularPeirceQuadratic_formula, circularPeirceQuadratic_formula,
    circularPeirceQuadratic_formula]
  simp only [Pi.add_apply]
  dsimp [circularPeirceBilinearForm]
  ring

/-- Every transported split-octonion automorphism preserves the full
polarized quadratic pairing, hence its positive and negative 4-dimensional
blocks are contragredient with respect to the signature `(+,-,-,-)` form. -/
theorem ellCoordinateAutomorphism_preserves_circularPeirceBilinearForm
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (x y : Fin 8 → ℝ) :
    circularPeirceBilinearForm (ellCoordinateAutomorphism φ x)
        (ellCoordinateAutomorphism φ y) = circularPeirceBilinearForm x y := by
  rw [circularPeirceBilinearForm_eq_quadratic_polarization,
    circularPeirceBilinearForm_eq_quadratic_polarization]
  calc
    circularPeirceQuadratic
        (ellCoordinateAutomorphism φ x + ellCoordinateAutomorphism φ y) -
        circularPeirceQuadratic (ellCoordinateAutomorphism φ x) -
        circularPeirceQuadratic (ellCoordinateAutomorphism φ y) =
      circularPeirceQuadratic
        (ellCoordinateAutomorphism φ (x + y)) -
        circularPeirceQuadratic (ellCoordinateAutomorphism φ x) -
        circularPeirceQuadratic (ellCoordinateAutomorphism φ y) := by
          rw [(ellCoordinateAutomorphism φ).map_add]
    _ = circularPeirceQuadratic (x + y) - circularPeirceQuadratic x -
        circularPeirceQuadratic y := by
          rw [ellCoordinateAutomorphism_preserves_circularPeirceQuadratic,
            ellCoordinateAutomorphism_preserves_circularPeirceQuadratic,
            ellCoordinateAutomorphism_preserves_circularPeirceQuadratic]

/-- Index embedding of the four positive Peirce coordinates into `Fin 8`. -/
def positivePeirceIndex (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩

/-- Index embedding of the four negative Peirce coordinates into `Fin 8`. -/
def negativePeirceIndex (i : Fin 4) : Fin 8 := ⟨i.val + 4, by omega⟩

/-- The signature matrix on a Peirce four-space: one positive scalar slot and
three negative root slots. -/
def peirceFourSignature (i : Fin 4) : ℝ := if i.val = 0 then 1 else -1

/-- The native split pairing of the images of a positive and a negative
Peirce basis vector is the original `(+,-,-,-)` pairing. Under the `lUnit`
stabilizer this becomes the relation between the two invariant blocks below. -/
theorem ellCoordinateAutomorphism_block_pairing
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (i j : Fin 4) :
    circularPeirceBilinearForm
        (ellCoordinateAutomorphism φ
          (Pi.single (positivePeirceIndex i) (1 : ℝ)))
        (ellCoordinateAutomorphism φ
          (Pi.single (negativePeirceIndex j) (1 : ℝ))) =
      if i = j then peirceFourSignature i else 0 := by
  rw [ellCoordinateAutomorphism_preserves_circularPeirceBilinearForm]
  fin_cases i <;> fin_cases j <;>
    norm_num [circularPeirceBilinearForm, positivePeirceIndex,
      negativePeirceIndex, peirceFourSignature, Pi.single_apply]

/-- The positive 4-by-4 block of the transported coordinate action. Its
columns are the positive-sector coordinates of images of positive basis
vectors. -/
def positivePeirceAutomorphismBlock
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
      (ellCoordinateAutomorphism φ
        (Pi.single (positivePeirceIndex j) (1 : ℝ))) (positivePeirceIndex i)

/-- The negative 4-by-4 block of the transported coordinate action. -/
def negativePeirceAutomorphismBlock
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
      (ellCoordinateAutomorphism φ
        (Pi.single (negativePeirceIndex j) (1 : ℝ))) (negativePeirceIndex i)

/-- Diagonal form `diag(1,-1,-1,-1)` on either Peirce four-space. -/
def peirceFourSignatureMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal peirceFourSignature

/-- Matrix form of the columnwise pairing theorem: the positive and negative
automorphism blocks satisfy `Uᵀ J V = J`, with `J = diag(1,-1,-1,-1)`. -/
theorem ellCoordinateAutomorphism_blocks_contragredient
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit) :
    Matrix.transpose (positivePeirceAutomorphismBlock φ) * peirceFourSignatureMatrix *
        negativePeirceAutomorphismBlock φ = peirceFourSignatureMatrix := by
  ext i j
  have hpair := ellCoordinateAutomorphism_block_pairing φ i j
  have hposInput : ∀ k : Fin 8, 4 ≤ k.val →
      ((Pi.single (positivePeirceIndex i) (1 : ℝ) : Coordinate) k) = 0 := by
    intro k hk
    have hne : k ≠ positivePeirceIndex i := by
      intro heq
      subst k
      simp [positivePeirceIndex] at hk
      omega
    simp [Pi.single_apply, hne]
  have hnegInput : ∀ k : Fin 8, k.val < 4 →
      ((Pi.single (negativePeirceIndex j) (1 : ℝ) : Coordinate) k) = 0 := by
    intro k hk
    have hne : k ≠ negativePeirceIndex j := by
      intro heq
      subst k
      simp [negativePeirceIndex] at hk
    simp [Pi.single_apply, hne]
  have hposOut := axisFixedAutomorphism_preserves_positive_coordinate_sector
    φ h_axis (Pi.single (positivePeirceIndex i) (1 : ℝ) : Coordinate) hposInput
  have hnegOut := axisFixedAutomorphism_preserves_negative_coordinate_sector
    φ h_axis (Pi.single (negativePeirceIndex j) (1 : ℝ) : Coordinate) hnegInput
  have hp4 := hposOut 4 (by decide)
  have hp5 := hposOut 5 (by decide)
  have hp6 := hposOut 6 (by decide)
  have hp7 := hposOut 7 (by decide)
  have hn0 := hnegOut 0 (by decide)
  have hn1 := hnegOut 1 (by decide)
  have hn2 := hnegOut 2 (by decide)
  have hn3 := hnegOut 3 (by decide)
  change (ellCoordinateAutomorphism φ
      (Pi.single (positivePeirceIndex i) (1 : ℝ) : Coordinate)) 4 = 0 at hp4
  change (ellCoordinateAutomorphism φ
      (Pi.single (positivePeirceIndex i) (1 : ℝ) : Coordinate)) 5 = 0 at hp5
  change (ellCoordinateAutomorphism φ
      (Pi.single (positivePeirceIndex i) (1 : ℝ) : Coordinate)) 6 = 0 at hp6
  change (ellCoordinateAutomorphism φ
      (Pi.single (positivePeirceIndex i) (1 : ℝ) : Coordinate)) 7 = 0 at hp7
  change (ellCoordinateAutomorphism φ
      (Pi.single (negativePeirceIndex j) (1 : ℝ) : Coordinate)) 0 = 0 at hn0
  change (ellCoordinateAutomorphism φ
      (Pi.single (negativePeirceIndex j) (1 : ℝ) : Coordinate)) 1 = 0 at hn1
  change (ellCoordinateAutomorphism φ
      (Pi.single (negativePeirceIndex j) (1 : ℝ) : Coordinate)) 2 = 0 at hn2
  change (ellCoordinateAutomorphism φ
      (Pi.single (negativePeirceIndex j) (1 : ℝ) : Coordinate)) 3 = 0 at hn3
  simp only [circularPeirceBilinearForm, hp4, hp5, hp6, hp7,
    hn0, hn1, hn2, hn3] at hpair
  simp only [peirceFourSignatureMatrix, Matrix.diagonal_apply] at ⊢
  rw [← hpair]
  simp [Matrix.mul_apply, Matrix.transpose_apply,
    positivePeirceAutomorphismBlock, negativePeirceAutomorphismBlock,
    peirceFourSignatureMatrix, Matrix.diagonal, peirceFourSignature,
    circularPeirceBilinearForm, positivePeirceIndex,
    negativePeirceIndex, Pi.single_apply, Fin.sum_univ_four] <;> ring

/-- The positive block fixes its scalar Peirce column. -/
theorem positivePeirceAutomorphismBlock_column_zero
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (i : Fin 4) :
    positivePeirceAutomorphismBlock φ i 0 = if i.val = 0 then 1 else 0 := by
  simp only [positivePeirceAutomorphismBlock, positivePeirceIndex]
  change (ellCoordinateAutomorphism φ (Pi.single 0 (1 : ℝ)))
    (positivePeirceIndex i) = _
  rw [axisFixedAutomorphism_fixes_uPlus_coordinate φ h_axis]
  fin_cases i <;> norm_num [positivePeirceIndex, Pi.single_apply]

/-- The negative block fixes its scalar Peirce column. -/
theorem negativePeirceAutomorphismBlock_column_zero
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (i : Fin 4) :
    negativePeirceAutomorphismBlock φ i 0 = if i.val = 0 then 1 else 0 := by
  simp only [negativePeirceAutomorphismBlock, negativePeirceIndex]
  change (ellCoordinateAutomorphism φ (Pi.single 4 (1 : ℝ))) (negativePeirceIndex i) = _
  rw [axisFixedAutomorphism_fixes_uMinus_coordinate φ h_axis]
  fin_cases i <;> norm_num [negativePeirceIndex, Pi.single_apply]

/-- Entrywise form of `Uᵀ J V = J`. -/
theorem ellCoordinateAutomorphism_blocks_contragredient_entry
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (i j : Fin 4) :
    (∑ k : Fin 4, positivePeirceAutomorphismBlock φ k i *
      peirceFourSignature k * negativePeirceAutomorphismBlock φ k j) =
      if i = j then peirceFourSignature i else 0 := by
  have hmat := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j)
    (ellCoordinateAutomorphism_blocks_contragredient φ h_axis)
  simpa [Matrix.mul_apply, Matrix.transpose_apply, peirceFourSignatureMatrix,
    Matrix.diagonal, Fin.sum_univ_four] using hmat

/-- The positive block also preserves the distinguished scalar row. -/
theorem positivePeirceAutomorphismBlock_row_zero
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (i : Fin 4) :
    positivePeirceAutomorphismBlock φ 0 i = if i.val = 0 then 1 else 0 := by
  have h := ellCoordinateAutomorphism_blocks_contragredient_entry φ h_axis i 0
  simp_rw [negativePeirceAutomorphismBlock_column_zero φ h_axis] at h
  simp [peirceFourSignature, Fin.sum_univ_four] at h
  by_cases hi : i = 0
  · subst i
    simpa [peirceFourSignature] using h
  · have hval : i.val ≠ 0 := by
      intro hv
      exact hi (Fin.ext hv)
    simpa [peirceFourSignature, hi, hval, eq_comm] using h

/-- The negative block also preserves the distinguished scalar row. -/
theorem negativePeirceAutomorphismBlock_row_zero
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (i : Fin 4) :
    negativePeirceAutomorphismBlock φ 0 i = if i.val = 0 then 1 else 0 := by
  have h := ellCoordinateAutomorphism_blocks_contragredient_entry φ h_axis 0 i
  simp_rw [positivePeirceAutomorphismBlock_column_zero φ h_axis] at h
  simp [peirceFourSignature, Fin.sum_univ_four] at h
  by_cases hi : i = 0
  · subst i
    simpa [peirceFourSignature] using h
  · have hval : i.val ≠ 0 := by
      intro hv
      exact hi (Fin.ext hv)
    simpa [peirceFourSignature, hi, hval, eq_comm] using h

/-- Root-coordinate indices are `1,2,3` inside a Peirce four-space. -/
def peirceRootIndex (i : Fin 3) : Fin 4 := ⟨i.val + 1, by omega⟩

/-- Positive root block, obtained by restricting the positive Peirce block to
its three root coordinates. -/
def positivePeirceRootBlock
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      positivePeirceAutomorphismBlock φ (peirceRootIndex i) (peirceRootIndex j)

/-- Negative root block, obtained by restricting the negative Peirce block to
its three root coordinates. -/
def negativePeirceRootBlock
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      negativePeirceAutomorphismBlock φ (peirceRootIndex i) (peirceRootIndex j)

/-- On the three root coordinates, the positive and negative blocks are
contragredient in the ordinary Euclidean pairing: `U₃ᵀ V₃ = I₃`. -/
theorem ellCoordinateAutomorphism_rootBlocks_inverseTranspose
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit) :
    Matrix.transpose (positivePeirceRootBlock φ) * negativePeirceRootBlock φ = 1 := by
  ext i j
  have h := ellCoordinateAutomorphism_blocks_contragredient_entry φ h_axis
    (peirceRootIndex i) (peirceRootIndex j)
  have hrow : positivePeirceAutomorphismBlock φ 0 (peirceRootIndex i) = 0 := by
    rw [positivePeirceAutomorphismBlock_row_zero φ h_axis]
    have hne : (peirceRootIndex i).val ≠ 0 := by simp [peirceRootIndex]
    simp [hne]
  have hidx : peirceRootIndex i = peirceRootIndex j ↔ i = j := by
    constructor
    · intro he
      apply Fin.ext
      have hv := congrArg Fin.val he
      simp [peirceRootIndex] at hv
      omega
    · rintro rfl
      rfl
  rw [Fin.sum_univ_four] at h
  simp only [peirceFourSignature, hidx] at h
  rw [hrow] at h
  simp only [zero_mul, zero_add] at h
  change (∑ k : Fin 3,
      positivePeirceAutomorphismBlock φ (peirceRootIndex k) (peirceRootIndex i) *
        negativePeirceAutomorphismBlock φ (peirceRootIndex k) (peirceRootIndex j)) =
      if i = j then 1 else 0
  rw [Fin.sum_univ_three]
  simp only [positivePeirceRootBlock, negativePeirceRootBlock,
    peirceRootIndex, peirceFourSignature] at h ⊢
  by_cases hij : i = j
  · subst j
    simp at h ⊢
    linarith
  · simp [hij] at h ⊢
    linarith

/-- The two root actions have reciprocal determinants, as forced by their
contragredient pairing. This does not by itself identify either determinant
with `1`; that stronger special-linear statement needs the root-product
compatibility of the split-octonion multiplication. -/
theorem ellCoordinateAutomorphism_rootBlocks_det_mul
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit) :
    Matrix.det (positivePeirceRootBlock φ) *
        Matrix.det (negativePeirceRootBlock φ) = 1 := by
  have hdet := congrArg Matrix.det
    (ellCoordinateAutomorphism_rootBlocks_inverseTranspose φ h_axis)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  exact hdet

theorem circularPeirceQuadratic_null_iff (X : CanonicalZorn) :
    circularPeirceQuadratic (coordinateEquiv X) = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X = 0 := by
  rw [circularPeirceQuadratic_apply]

theorem detZ_null_iff_circularPeirceQuadratic_null (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X = 0 ↔
      circularPeirceQuadratic (coordinateEquiv X) = 0 := by
  rw [circularPeirceQuadratic_apply]

theorem detZ_coordinate_zero_iff (X : CanonicalZorn) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X = 0 ↔
      coordinateEquiv X 0 * coordinateEquiv X 4 =
        coordinateEquiv X 1 * coordinateEquiv X 5 +
          coordinateEquiv X 2 * coordinateEquiv X 6 +
          coordinateEquiv X 3 * coordinateEquiv X 7 := by
  rw [← circularPeirceQuadratic_apply X,
    circularPeirceQuadratic_zero_iff]

theorem circularPeirceQuadratic_axialFlowCoordinate (t : ℝ) (x : Fin 8 → ℝ) :
    circularPeirceQuadratic (axialFlowCoordinate t x) =
      circularPeirceQuadratic x := by
  rw [circularPeirceQuadratic_formula, circularPeirceQuadratic_formula]
  dsimp [axialFlowCoordinate]
  simp only [axialWeight, mul_zero, Real.exp_zero, one_mul, mul_one,
    mul_neg]
  rw [reciprocal_exponential_channel_invariant,
    reciprocal_exponential_channel_invariant,
    reciprocal_exponential_channel_invariant]

theorem circularPeirceQuadratic_axialFlowCoordinate_zero_iff
    (t : ℝ) (x : Fin 8 → ℝ) :
    circularPeirceQuadratic (axialFlowCoordinate t x) = 0 ↔
      circularPeirceQuadratic x = 0 := by
  rw [circularPeirceQuadratic_axialFlowCoordinate]

theorem circularPeirceQuadratic_axialFlow_zero_iff
    (t : ℝ) (X : CanonicalZorn) :
    circularPeirceQuadratic (coordinateEquiv (axialFlow t X)) = 0 ↔
      circularPeirceQuadratic (coordinateEquiv X) = 0 := by
  have hcoord : coordinateEquiv (axialFlow t X) =
      axialFlowCoordinate t (coordinateEquiv X) := by
    funext i
    exact coordinateEquiv_axialFlow_apply t X i
  rw [hcoord, circularPeirceQuadratic_axialFlowCoordinate]

noncomputable def circularPeirceQuadraticIsometry :
    canonicalDetQuadratic.IsometryEquiv circularPeirceQuadratic :=
  QuadraticMap.IsometryEquiv.mk circularPeirceBasis.equivFun (by
    intro X
    change circularPeirceQuadratic (coordinateEquiv X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X
    exact circularPeirceQuadratic_apply X)

@[simp] theorem circularPeirceQuadraticIsometry_map_app (X : CanonicalZorn) :
    circularPeirceQuadratic (circularPeirceQuadraticIsometry X) =
      canonicalDetQuadratic X :=
  circularPeirceQuadraticIsometry.map_app X

@[simp] theorem circularPeirceQuadraticIsometry_symm_map_app
    (x : Fin 8 → ℝ) :
    canonicalDetQuadratic (circularPeirceQuadraticIsometry.symm x) =
      circularPeirceQuadratic x :=
  circularPeirceQuadraticIsometry.symm.map_app x

end InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates

namespace InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinatesWitnesses

theorem peirceBlock4_noncomm :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 4)) (0 : Fin 4)
  have hAB : (A * B) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 4)]
    · simp [A, B]
    · intro k _ hk
      simp [A, hk]
    · intro h1
      exact (h1 (Finset.mem_univ _)).elim
  have hBA : (B * A) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun k _ => by simp [B])
  rw [hAB, hBA] at h00
  exact one_ne_zero h00

theorem crossProduct3_mat3_noncomm :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 3)) (0 : Fin 3)
  have hAB : (A * B) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 3)]
    · simp [A, B]
    · intro k _ hk
      simp [A, hk]
    · intro h1
      exact (h1 (Finset.mem_univ _)).elim
  have hBA : (B * A) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun k _ => by simp [B])
  rw [hAB, hBA] at h00
  exact one_ne_zero h00

end InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinatesWitnesses
