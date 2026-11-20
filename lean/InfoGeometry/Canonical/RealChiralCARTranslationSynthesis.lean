/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.RealGradedZornCARBridge
import InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
import InfoGeometry.Quantum.Realification
import InfoGeometry.Quantum.RealificationCategory

/-!
# Shared real carrier synthesis: circular CAR and Peirce translations

Both constructions act on the same real doubled-Krein carrier through the
three-factor Koszul-graded product of real `2 × 2` matrices. At unit time-like
momentum, their anticommutators have the same value, the identity. This is an
operator-level comparison of anticommutators; it does not identify the two
charge pairs term by term.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealChiralCARTranslationSynthesis

open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
open InfoGeometry.Superalgebra.RealGradedZornCARBridge
open InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Canonical.GradedTensorWeylBridge
open Matrix
open scoped TensorProduct GradedTensorProduct

local notation "FourSpace" => InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace
local notation "KreinFrame4" => InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4

/-! ### Realification of the Yang--Mills operator on the doubled carrier

The source Yang--Mills owner writes its finite connection and curvature as
complex `4 × 4` matrices.  Here the coefficients are realified using the
existing faithful realification owner, with real and imaginary coordinates
identified with the two components of `KreinFrame4`.  The induced phase
operator is proved to be the existing doubled real complex structure. -/

/-- Coordinates on `KreinFrame4` ordered as the real and imaginary blocks of
the realification of a complex four-vector. -/
noncomputable def realificationKreinFrameEquiv :
    (Fin 4 ⊕ Fin 4 → ℝ) ≃ₗ[ℝ] KreinFrame4 where
  toFun x := InfoGeometry.Krein.to_doubled
    (WithLp.toLp 2 (fun i => x (.inl i)))
    (WithLp.toLp 2 (fun i => x (.inr i)))
  invFun u := Sum.elim (fun i => (WithLp.fst u).ofLp i)
    (fun i => (WithLp.snd u).ofLp i)
  left_inv x := by
    funext i
    cases i <;> simp
  right_inv u := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      simp [WithLp.toLp, WithLp.ofLp_toLp]
  map_add' x y := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      simp only [InfoGeometry.Krein.to_doubled, WithLp.add_fst, WithLp.add_snd]
    all_goals
      rw [← WithLp.toLp_add]
      congr 1
  map_smul' r x := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      simp only [InfoGeometry.Krein.to_doubled, WithLp.smul_fst, WithLp.smul_snd]
    all_goals
      rw [← WithLp.toLp_smul]
      congr 1

/-- A complex matrix acting on `ℂ⁴`, transported through realification to a
real-linear endomorphism of the existing doubled Krein carrier. -/
def realifiedCircularMatrixEnd (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Module.End ℝ KreinFrame4 :=
  (realificationKreinFrameEquiv.conjAlgEquiv ℝ)
    (Matrix.toLinAlgEquiv'
      (InfoGeometry.Quantum.Realification.realify A))

/-- Realification and the real coordinate equivalence preserve ordered
matrix composition on `KreinFrame4`. -/
theorem realifiedCircularMatrixEnd_mul
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    realifiedCircularMatrixEnd (A * B) =
      realifiedCircularMatrixEnd A * realifiedCircularMatrixEnd B := by
  simp [realifiedCircularMatrixEnd,
    InfoGeometry.Quantum.Realification.realify_mul]

/-- The internal realification phase is exactly the existing doubled real
complex structure after the real/imaginary coordinate identification. -/
theorem realificationKreinFrameEquiv_internalJ :
    (realificationKreinFrameEquiv.conjAlgEquiv ℝ)
      (Matrix.toLinAlgEquiv'
        (InfoGeometry.Quantum.Realification.internalJ (n := Fin 4))) =
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap := by
  apply LinearMap.ext
  intro u
  have hcoord : realificationKreinFrameEquiv.symm u =
      Sum.elim (fun i => (WithLp.fst u).ofLp i)
        (fun i => (WithLp.snd u).ofLp i) := rfl
  change realificationKreinFrameEquiv
      (Matrix.toLinAlgEquiv'
        (InfoGeometry.Quantum.Realification.internalJ (n := Fin 4))
        (realificationKreinFrameEquiv.symm u)) = _
  rw [hcoord, Matrix.toLinAlgEquiv'_apply]
  have hmul :
      InfoGeometry.Quantum.Realification.internalJ (n := Fin 4) *ᵥ
          Sum.elim (fun i => (WithLp.fst u).ofLp i)
            (fun i => (WithLp.snd u).ofLp i) =
        Sum.elim (fun i => -(WithLp.snd u).ofLp i)
          (fun i => (WithLp.fst u).ofLp i) := by
    calc
      _ = InfoGeometry.Quantum.Realification.internalJ *ᵥ
          InfoGeometry.Quantum.Realification.realifyVector
            (InfoGeometry.Quantum.Realification.unrealifyVector
              (Sum.elim (fun i => (WithLp.fst u).ofLp i)
                (fun i => (WithLp.snd u).ofLp i))) := by
              rw [InfoGeometry.Quantum.Realification.realifyVector_unrealifyVector]
      _ = InfoGeometry.Quantum.Realification.realifyVector
          (Complex.I • InfoGeometry.Quantum.Realification.unrealifyVector
            (Sum.elim (fun i => (WithLp.fst u).ofLp i)
              (fun i => (WithLp.snd u).ofLp i))) :=
            InfoGeometry.Quantum.Realification.internalJ_realifyVector _
      _ = _ := by
        ext i
        cases i <;>
          simp [InfoGeometry.Quantum.Realification.realifyVector,
            InfoGeometry.Quantum.Realification.unrealifyVector,
            Complex.I_mul]
  rw [hmul]
  change InfoGeometry.Krein.to_doubled
      (WithLp.toLp 2 (fun i => -(WithLp.snd u).ofLp i))
      (WithLp.toLp 2 (fun i => (WithLp.fst u).ofLp i)) = _
  exact (InfoGeometry.Krein.complex_i_to_doubled
    (WithLp.fst u) (WithLp.snd u)).symm

/-- Every realified Yang--Mills matrix commutes with the actual doubled real
complex structure; no complex scalar action is introduced on `KreinFrame4`. -/
theorem realifiedCircularMatrixEnd_commutes_complexStructure
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Commute (realifiedCircularMatrixEnd A)
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap := by
  have h := InfoGeometry.Quantum.Realification.realify_commutes_internalJ A
  have h' := congrArg
    (fun M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ =>
      (realificationKreinFrameEquiv.conjAlgEquiv ℝ) (Matrix.toLinAlgEquiv' M)) h.eq
  have hJ := realificationKreinFrameEquiv_internalJ
  change realifiedCircularMatrixEnd A *
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap =
    InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap *
      realifiedCircularMatrixEnd A
  simpa [realifiedCircularMatrixEnd, hJ] using h'

/-- The real operator curvature of the existing circular Yang--Mills
connection is the ordered square of its realified connection on `KreinFrame4`.
This is a curvature bridge on the real carrier, before any trace/action
readout. -/
theorem realifiedCircularCurvature_eq_connection_square (x : Coordinate) :
    realifiedCircularMatrixEnd (circularCurvatureMat4 x) =
      realifiedCircularMatrixEnd (circularConnectionMat4 x) *
        realifiedCircularMatrixEnd (circularConnectionMat4 x) := by
  rw [circularCurvatureMat4, realifiedCircularMatrixEnd_mul]

/-! ### Real Weyl channel in the two-factor Koszul tensor

The circular Weyl matrix is realified and represented in the existing native
`M₂(ℝ) ᵍ⊗ M₂(ℝ)` carrier. The elliptic Pauli direction is retained as the
odd-odd tensor term, so the displayed representation uses the Koszul sign
rather than an ungraded block embedding.
-/

private def realPauliX : Matrix (Fin 2) (Fin 2) ℝ :=
  matrixE01 + matrixE10

private def realPauliEpsilon : Matrix (Fin 2) (Fin 2) ℝ :=
  matrixE10 - matrixE01

private def realPauliZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def realWeylUpperTensor (x : Coordinate) : twoMatrixGradedTensor :=
  x 0 • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ᵍ⊗ₜ[ℝ]
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
  x 1 • (realPauliZ ᵍ⊗ₜ[ℝ] realPauliX) +
  x 2 • (realPauliX ᵍ⊗ₜ[ℝ] realPauliEpsilon) +
  x 3 • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ᵍ⊗ₜ[ℝ]
      realPauliZ)

theorem realWeylUpperTensor_represents_weylUpperMat (x : Coordinate) :
    realNestedMatrixToFin4
        (twoMatrixGradedTensorMoritaEquiv (realWeylUpperTensor x)) =
      InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify
        (weylUpperMat x) := by
  rw [show weylUpperMat x =
      !![(x 0 : ℂ) + x 3, (x 1 : ℂ) - Complex.I * x 2;
        (x 1 : ℂ) + Complex.I * x 2, (x 0 : ℂ) - x 3] by
        simp [weylUpperMat, pauliSolder2x2, solder_explicit]]
  simp only [realWeylUpperTensor, map_add, map_smul,
    twoMatrixGradedTensorMoritaEquiv_tmul]
  let e : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  have hto (A : Matrix (Fin 2) (Fin 2) M2R) (i j : Fin 4) :
      realNestedMatrixToFin4 A i j =
        A (e.symm i).1 (e.symm j).1 (e.symm i).2 (e.symm j).2 := by
    rfl
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, hto]
  simp only [InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify_apply]
  fin_cases i <;> fin_cases j <;>
    dsimp [e, finProdFinEquiv] <;>
    simp [realNestedMatrixToFin4, realNestedMatrixFlatten,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.head,
      matrixE01, matrixE10, Matrix.algebraMap_matrix_apply,
      realPauliX, realPauliEpsilon, realPauliZ,
      twoMatrixGradedTensorToCl11Tensor_tmul,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.tensorMatrixEquiv_apply,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.tensorToMatrix_tmul,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.head_apply,
      InfoGeometry.Clifford.Cl11GradedTensorMorita.tail_apply,
      AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv,
      Matrix.reindex_apply,
      InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify,
      InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.reindexBlock,
      InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.blockRealify,
      matrixParity_apply, Matrix.single, finProdFinEquiv,
      Fin.divNat, Fin.modNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The unit time-like vector in the real `FourSpace` coordinate convention. -/
def unitTimeMomentum : FourSpace :=
  fourSpaceEquivVec22.symm (1, 0, 0, 0)

/-- Real Pauli soldering sends unit time momentum to the identity matrix. -/
theorem realMomentum_unitTime : realMomentum unitTimeMomentum = 1 := by
  unfold realMomentum unitTimeMomentum
  rw [fourSpaceEquivVec22.apply_symm_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Clifford.Soldering.soldering,
    InfoGeometry.Clifford.Soldering.sigma0,
    InfoGeometry.Clifford.Soldering.sigma1,
    InfoGeometry.Clifford.Soldering.sigma3,
    InfoGeometry.Clifford.Soldering.epsilon]

/-- The diagonal momentum block at unit time is the identity on the two
Peirce sheets. -/
theorem diagonalMomentumOperator_unitTime :
    diagonalMomentumOperator unitTimeMomentum =
      (1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ)) := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [diagonalMomentumOperator, realMomentum_unitTime,
      Matrix.zero_apply]

/-- The three-mode doubled-Krein representation of unit-time diagonal
momentum is the identity operator. -/
theorem realThreeKrein_unitTimeMomentum_is_one :
    realThreeMatrixTensorOnH4 (realTwoMatrixPairIntoThreeMode
      (twoMatrixGradedTensorMoritaEquiv.symm
        (diagonalMomentumOperator unitTimeMomentum))) = 1 := by
  rw [diagonalMomentumOperator_unitTime]
  simp

/-- On the common real doubled-Krein carrier, the circular split-octonion
root CAR anticommutator equals the anticommutator of the real Peirce
translation and its complementary charge at unit time-like momentum.

The theorem identifies the resulting operator-valued momentum readout (the
identity at this normalized point), not the individual root and translation
operators. -/
theorem circularRootCAR_matches_unitTime_translation (i : Fin 3) :
    realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootMinus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootPlus i))) +
      realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootPlus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootMinus i))) =
      realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode (translationInGradedTensor unitTimeMomentum)) *
        realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode conjugatePeirceCharge) +
      realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode conjugatePeirceCharge) *
        realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode (translationInGradedTensor unitTimeMomentum)) := by
  rw [threeMode_supercolor_root_CAR i,
    realKrein_gradedPair_translationCharge_anticommutator_eq_diagonalMomentum,
    realThreeKrein_unitTimeMomentum_is_one]

end InfoGeometry.Canonical.RealChiralCARTranslationSynthesis
