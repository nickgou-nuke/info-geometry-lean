/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesEvenPauliEquiv
import InfoGeometry.Canonical.Cl11JordanComplexCommutantEquiv
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge
import InfoGeometry.Canonical.RealChiralCARTranslationSynthesis

/-!
# Real Hestenes algebra inside the Koszul graded matrix tensor

The real even Clifford algebra `Cl⁺(1,3)` acts through its real Pauli
equivalence into the realification of `M₂(ℂ)`. The image lies in the
commutant of the real operator `J` with `J² = -1`; it then embeds into the
full real matrix algebra represented by the genuine Koszul graded tensor of
two real `M₂(ℝ)` factors. This is an embedding into a real operator algebra,
not a change of scalar field or an identification of the smaller Clifford
algebra with the full 16-dimensional matrix algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation

open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Canonical.Cl11JordanComplexCommutantEquiv
open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.GradedTensorWeylBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge
open InfoGeometry.Canonical.RealChiralCARTranslationSynthesis
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Quantum.PauliSoldering
open HestenesPauliSheetBridge
open HestenesCl14
open Matrix
open scoped TensorProduct GradedTensorProduct

local notation "M4R" => InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.Mat4R
local notation "Tensor2" => InfoGeometry.Canonical.GradedTensorWeylBridge.twoMatrixGradedTensor
local notation "Tensor3" => InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realThreeMatrixGradedTensor
local notation "HestenesEven" => HestenesCl14.ClPlus14
local notation "KreinFrame4" => InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4
local notation "FockCarrier" => Matrix (Fin 8) (Fin 8) ℝ

/-- Include the real commutant algebra into the full real `4 × 4` matrix
algebra. -/
def commutantToMatrix : commutantSubalgebra →ₐ[ℝ] M4R :=
  commutantSubalgebra.val

/-- The native real Hestenes even algebra embedded in the two-factor
Koszul-graded tensor of real `2 × 2` matrix algebras. -/
def hestenesEvenToRealGradedTensor : HestenesEven →ₐ[ℝ] Tensor2 :=
  (twoMatrixGradedTensorMoritaEquiv.symm.toAlgHom.comp
      realNestedMatrixToFin4.symm.toAlgHom).comp
    ((commutantToMatrix.comp realifyCommutantHom).comp
      HestenesEvenPauliEquiv.clPlusPauliAlgEquiv)

/-- The real graded-tensor representation of a Hestenes-even element has
exactly the realified Pauli matrix as its nested-matrix readout. -/
theorem hestenesEvenToRealGradedTensor_readout (a : HestenesEven) :
    realNestedMatrixToFin4
        (twoMatrixGradedTensorMoritaEquiv (hestenesEvenToRealGradedTensor a)) =
      Cl11JordanComplexRealificationBridge.realify
        (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv a) := by
  simp [hestenesEvenToRealGradedTensor, commutantToMatrix,
    Cl11JordanComplexCommutantEquiv.realifyCommutantHom,
    Cl11JordanComplexRealificationBridge.realifyRingHom]

/-! ### Circular Weyl channels inside the real Hestenes even algebra

The circular upper Weyl channel and the real Hestenes even algebra are two
constructions of the same Pauli operator. The coefficient field of the
Clifford element remains `ℝ`; the real Pauli equivalence records the complex
structure internally and the graded-tensor image is the already-owned real
operator tensor.
-/

/-- The real `Cl⁺(1,3)` element whose Pauli image is the upper circular Weyl
channel. Its coefficients are real and its three spatial generators are the
owner's even Clifford bivectors `sigmaEven 0`, `sigmaEven 1`, `sigmaEven 2`. -/
def circularWeylUpperEven
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    HestenesEven :=
  x 0 • (1 : HestenesEven) + x 1 • sigmaEven 0 +
    x 2 • sigmaEven 1 + x 3 • sigmaEven 2

/-- Under the genuine real Pauli equivalence, the real Hestenes element above
is exactly the circular upper Weyl matrix. -/
theorem clPlusPauli_circularWeylUpperEven
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    HestenesPauliSheetBridge.clPlusToPauli (circularWeylUpperEven x) =
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x := by
  simp only [circularWeylUpperEven, map_add, map_smul, map_one,
    HestenesEvenPauliEquiv.clPlusToPauli_sigma0,
    HestenesEvenPauliEquiv.clPlusToPauli_sigma1,
    HestenesEvenPauliEquiv.clPlusToPauli_sigma2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat,
      pauliSolder2x2, solder, σ0, σ1, σ2, σ3,
      HestenesEvenPauliEquiv.pauli1, HestenesEvenPauliEquiv.pauli2,
      HestenesEvenPauliEquiv.pauli3]

/-- Exact coefficient-level identification of the circular upper Weyl
channel with its real Hestenes-even element in the native two-factor
Koszul-graded tensor. The existing three-mode inclusion and doubled-Krein
action therefore apply to this same operator. -/
theorem circularWeylUpperTensor_eq_hestenesEven_image
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    realWeylUpperTensor x =
      hestenesEvenToRealGradedTensor (circularWeylUpperEven x) := by
  have hPauli :
      HestenesEvenPauliEquiv.clPlusPauliAlgEquiv (circularWeylUpperEven x) =
        InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x := by
    change HestenesPauliSheetBridge.clPlusToPauli (circularWeylUpperEven x) = _
    exact clPlusPauli_circularWeylUpperEven x
  apply twoMatrixGradedTensorMoritaEquiv.injective
  apply realNestedMatrixToFin4.injective
  calc
    realNestedMatrixToFin4
        (twoMatrixGradedTensorMoritaEquiv (realWeylUpperTensor x)) =
        Cl11JordanComplexRealificationBridge.realify
          (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x) :=
      realWeylUpperTensor_represents_weylUpperMat x
    _ = Cl11JordanComplexRealificationBridge.realify
        (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv (circularWeylUpperEven x)) :=
      congrArg Cl11JordanComplexRealificationBridge.realify
        hPauli.symm
    _ = realNestedMatrixToFin4
        (twoMatrixGradedTensorMoritaEquiv
          (hestenesEvenToRealGradedTensor (circularWeylUpperEven x))) := by
      simp [hestenesEvenToRealGradedTensor, commutantToMatrix,
        Cl11JordanComplexCommutantEquiv.realifyCommutantHom,
        Cl11JordanComplexRealificationBridge.realifyRingHom]

/-- The represented real Weyl generators retain noncommutative content in
the real `2 × 2` graded tensor. This explicit witness is also the reason the
real carrier cannot be replaced by a scalar or diagonal surrogate. -/
def realWeylRootPlus0 : Tensor2 :=
  realWeylUpperTensor
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0))

def realWeylRootPlus1 : Tensor2 :=
  realWeylUpperTensor
    (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1))

theorem realWeylUpperTensor_rootPlus_noncommute :
    realWeylRootPlus0 * realWeylRootPlus1 ≠
      realWeylRootPlus1 * realWeylRootPlus0 := by
  intro h
  dsimp [realWeylRootPlus0, realWeylRootPlus1] at h
  let E := twoMatrixGradedTensorMoritaEquiv.trans realNestedMatrixToFin4
  let x₀ := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
    (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0)
  let x₁ := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
    (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1)
  have hReal := congrArg E h
  rw [map_mul, map_mul] at hReal
  change realNestedMatrixToFin4 (twoMatrixGradedTensorMoritaEquiv
      (realWeylUpperTensor x₀)) *
      realNestedMatrixToFin4 (twoMatrixGradedTensorMoritaEquiv
        (realWeylUpperTensor x₁)) =
    realNestedMatrixToFin4 (twoMatrixGradedTensorMoritaEquiv
      (realWeylUpperTensor x₁)) *
      realNestedMatrixToFin4 (twoMatrixGradedTensorMoritaEquiv
        (realWeylUpperTensor x₀)) at hReal
  rw [realWeylUpperTensor_represents_weylUpperMat x₀,
    realWeylUpperTensor_represents_weylUpperMat x₁] at hReal
  have hComplex :
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₀ *
        InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₁ =
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₁ *
        InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₀ := by
    apply Cl11JordanComplexRealificationBridge.realify_injective
    calc
      _ = Cl11JordanComplexRealificationBridge.realify
          (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₀) *
          Cl11JordanComplexRealificationBridge.realify
            (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₁) :=
        Cl11JordanComplexRealificationBridge.realify_mul _ _
      _ = Cl11JordanComplexRealificationBridge.realify
          (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₁) *
          Cl11JordanComplexRealificationBridge.realify
            (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₀) := hReal
      _ = Cl11JordanComplexRealificationBridge.realify
          (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₁ *
            InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x₀) :=
        (Cl11JordanComplexRealificationBridge.realify_mul _ _).symm
  exact InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat_rootPlus_comm.2 hComplex

/-- The lower circular sheet is presented in the upper Weyl coordinates by
the source owner's signed lower-coordinate map; unused upper-sheet entries
are zero. -/
def circularWeylLowerCoordinates
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate :=
  ![InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularSignedMinusCoord x 0,
    InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularSignedMinusCoord x 1,
    InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularSignedMinusCoord x 2,
    InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularSignedMinusCoord x 3,
    0, 0, 0, 0]

/-- The signed lower Peirce sheet has exactly the lower Weyl soldering matrix
when read through the existing upper-channel coordinates. -/
theorem weylUpperMat_circularWeylLowerCoordinates
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat
        (circularWeylLowerCoordinates x) =
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylLowerMat x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularWeylLowerCoordinates,
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.circularSignedMinusCoord,
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat,
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylLowerMat,
      pauliSolder2x2,
      solder,
      σ0,
      σ1,
      σ2,
      σ3]

/-- The real Hestenes-even operator obtained from the signed lower sheet
realifies to the existing lower Weyl block. This is the lower-channel
counterpart to the upper tensor identity above. -/
theorem hestenesEven_lowerWeyl_block_realification
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    realNestedMatrixToFin4
        (twoMatrixGradedTensorMoritaEquiv
          (hestenesEvenToRealGradedTensor
            (circularWeylUpperEven (circularWeylLowerCoordinates x)))) =
      Cl11JordanComplexRealificationBridge.realify
        (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylLowerMat x) := by
  rw [← circularWeylUpperTensor_eq_hestenesEven_image]
  rw [realWeylUpperTensor_represents_weylUpperMat,
    weylUpperMat_circularWeylLowerCoordinates]

/-- The commutator of the real Hestenes representatives of the two circular
Weyl channels is the vorticity operator. On the real four-dimensional
readout, its phase factor is the existing internal complex-structure
operator; the Hestenes algebra and its graded-tensor carrier remain real. -/
theorem hestenesEven_circularWeyl_commutator_vorticity
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    realNestedMatrixToFin4
        (twoMatrixGradedTensorMoritaEquiv
          (hestenesEvenToRealGradedTensor
            (circularWeylUpperEven x *
                circularWeylUpperEven (circularWeylLowerCoordinates x) -
              circularWeylUpperEven (circularWeylLowerCoordinates x) *
                circularWeylUpperEven x))) =
      (-2 : ℝ) • (complexStructure *
        Cl11JordanComplexRealificationBridge.realify
          (solder (0,
            (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 0 : ℂ),
            (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 1 : ℂ),
            (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 2 : ℂ)))) := by
  have hUpper : HestenesEvenPauliEquiv.clPlusPauliAlgEquiv
      (circularWeylUpperEven x) =
        InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x := by
    change HestenesPauliSheetBridge.clPlusToPauli (circularWeylUpperEven x) = _
    exact clPlusPauli_circularWeylUpperEven x
  have hLower : HestenesEvenPauliEquiv.clPlusPauliAlgEquiv
      (circularWeylUpperEven (circularWeylLowerCoordinates x)) =
        InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylLowerMat x := by
    calc
      _ = InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat
          (circularWeylLowerCoordinates x) :=
            clPlusPauli_circularWeylUpperEven (circularWeylLowerCoordinates x)
      _ = InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylLowerMat x :=
        weylUpperMat_circularWeylLowerCoordinates x
  rw [hestenesEvenToRealGradedTensor_readout]
  rw [map_sub, map_mul, map_mul, hUpper, hLower]
  rw [InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylChannel_commutator_eq_vorticity]
  let V : Matrix (Fin 2) (Fin 2) ℂ :=
    solder (0,
      (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 0 : ℂ),
      (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 1 : ℂ),
      (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 2 : ℂ))
  have hsmul : ((-2 * Complex.I : ℂ) • V) =
      (-2 : ℝ) • ((Complex.I : ℂ) • V) := by
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul]
    ring
  calc
    Cl11JordanComplexRealificationBridge.realify ((-2 * Complex.I : ℂ) • V) =
        Cl11JordanComplexRealificationBridge.realify
          ((-2 : ℝ) • ((Complex.I : ℂ) • V)) := by rw [hsmul]
    _ = (-2 : ℝ) • Cl11JordanComplexRealificationBridge.realify
          ((Complex.I : ℂ) • V) :=
        Cl11JordanComplexRealificationBridge.realify_real_smul _ _
    _ = (-2 : ℝ) • (complexStructure *
          Cl11JordanComplexRealificationBridge.realify V) := by
        rw [Cl11JordanComplexRealificationBridge.realify_I_smul_eq_complexStructure_mul]
    _ = _ := rfl

/-- The real tensor representation, diagonally lifted to the doubled
Krein/Hestenes carrier. -/
def hestenesEvenOnDoubledKrein : HestenesEven →ₐ[ℝ]
    Module.End ℝ KreinFrame4 :=
  (doubleEndAlgHom.comp realTwoMatrixGradedTensorOnFourSpace.toAlgHom).comp
    hestenesEvenToRealGradedTensor

/-- The same circular Weyl commutator acts on the doubled real Krein carrier
as the doubled real operator `J · vorticity`. This is the operator-level
Yang--Mills/Hestenes bridge; `J` is the existing real complex-structure
endomorphism encoded by `complexStructure`, not a complex scalar field. -/
theorem hestenesEven_circularWeyl_commutator_vorticity_onKrein
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    hestenesEvenOnDoubledKrein
        (circularWeylUpperEven x *
            circularWeylUpperEven (circularWeylLowerCoordinates x) -
          circularWeylUpperEven (circularWeylLowerCoordinates x) *
            circularWeylUpperEven x) =
      doubleEnd ((LinearMap.toMatrixAlgEquiv
        (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).symm
          ((-2 : ℝ) • (complexStructure *
            Cl11JordanComplexRealificationBridge.realify
              (solder (0,
                (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 0 : ℂ),
                (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 1 : ℂ),
                (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.chiralVorticityVec x 2 : ℂ)))))) := by
  change doubleEnd ((LinearMap.toMatrixAlgEquiv
      (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).symm
        (realNestedMatrixToFin4
          (twoMatrixGradedTensorMoritaEquiv
            (hestenesEvenToRealGradedTensor
              (circularWeylUpperEven x *
                  circularWeylUpperEven (circularWeylLowerCoordinates x) -
                circularWeylUpperEven (circularWeylLowerCoordinates x) *
                  circularWeylUpperEven x))))) = _
  rw [hestenesEven_circularWeyl_commutator_vorticity]

/-- Include the native real Hestenes algebra into the three-factor Koszul
graded tensor used by the three-mode Fock and circular-CAR owners. -/
def hestenesEvenToThreeModeTensor : HestenesEven →ₐ[ℝ] Tensor3 :=
  InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoModeIntoThreeMode.comp
    hestenesEvenToRealGradedTensor

/-- Real Fock-matrix realization of the Hestenes even algebra, transported
through the existing Fock-to-three-mode graded-tensor equivalence. -/
def hestenesEvenToFockMatrix : HestenesEven →ₐ[ℝ] FockCarrier :=
  (fockMatrixToRealGradedTensor.symm.toAlgHom).comp
    hestenesEvenToThreeModeTensor

/-- The three-mode tensor action of a Hestenes even element is exactly its
existing doubled-Krein representation. -/
theorem hestenesEven_threeMode_action (x : HestenesEven) :
    realThreeMatrixTensorOnH4 (hestenesEvenToThreeModeTensor x) =
      hestenesEvenOnDoubledKrein x := by
  simpa [hestenesEvenToThreeModeTensor, hestenesEvenOnDoubledKrein,
    doubleEndAlgHom] using
      realThreeMatrixTensorOnH4_twoModeIntoThreeMode
        (hestenesEvenToRealGradedTensor x)

/-- The existing three-mode CAR action of the circular upper Weyl channel is
the same doubled-Krein operator as its real Hestenes-even representative. -/
theorem circularWeylUpper_threeMode_action
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate) :
    realThreeMatrixTensorOnH4
        (InfoGeometry.Canonical.RealSolderingWeylKreinBridge.twoModeIntoThreeMode
          (realWeylUpperTensor x)) =
      hestenesEvenOnDoubledKrein (circularWeylUpperEven x) := by
  rw [circularWeylUpperTensor_eq_hestenesEven_image,
    realThreeMatrixTensorOnH4_twoModeIntoThreeMode]
  rfl

/- The CAR creation operator attached to a circular `rootPlus` channel is
not the Pauli/Clifford vector obtained by soldering the same coordinate
vector. Both operators act on the same doubled real Krein carrier, but their
products distinguish their roles: right-regular multiplication by the Zorn
root is square-zero, whereas the soldered Weyl vector squares to the
identity. The shared coordinate label therefore does not identify the
operator-algebra CAR generator with the spacetime Clifford generator. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem circularRootPlus_creation_ne_solderedWeyl_vector (i : Fin 3) :
    realThreeMatrixTensorOnH4 (circularRootPlusInTensor i) ≠
      doubleEnd (realTwoMatrixGradedTensorOnFourSpace
        (realWeylUpperTensor
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i)))) := by
  intro hEq
  have hSq := congrArg (fun A : Module.End ℝ KreinFrame4 => A * A) hEq
  have hCreationSq :
      realThreeMatrixTensorOnH4 (circularRootPlusInTensor i) *
        realThreeMatrixTensorOnH4 (circularRootPlusInTensor i) = 0 := by
    have hTensorSq : circularRootPlusInTensor i * circularRootPlusInTensor i = 0 := by
      apply realThreeMatrixTensorOnH4.injective
      unfold circularRootPlusInTensor
      rw [map_mul,
      InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
      realThreeMatrixTensorOnH4.apply_symm_apply,
      InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical,
      InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_rootPlus_sq,
      map_zero]
    rw [← map_mul, hTensorSq, map_zero]
  have hWeylSq :
      doubleEnd (realTwoMatrixGradedTensorOnFourSpace
        (realWeylUpperTensor
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i)))) *
      doubleEnd (realTwoMatrixGradedTensorOnFourSpace
        (realWeylUpperTensor
          (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i)))) = 1 := by
    let x := InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i)
    have hTensorSq : realWeylUpperTensor x ^ 2 = 1 := by
      let E := twoMatrixGradedTensorMoritaEquiv.trans realNestedMatrixToFin4
      have hRep : E (realWeylUpperTensor x) =
          InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify
            (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x) :=
        realWeylUpperTensor_represents_weylUpperMat x
      have hPauliSq :
          (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x) ^ 2 = 1 := by
        rw [show x = InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv
            (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i) by rfl,
          InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat_rootPlus]
        rw [pow_two]
        fin_cases i <;>
          ext a b <;> fin_cases a <;> fin_cases b <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two,
            InfoGeometry.Quantum.PauliSoldering.σ1,
            InfoGeometry.Quantum.PauliSoldering.σ2,
            InfoGeometry.Quantum.PauliSoldering.σ3, Complex.I_mul_I]
      apply E.injective
      calc
        E (realWeylUpperTensor x ^ 2) = E (realWeylUpperTensor x) ^ 2 := by rw [map_pow]
        _ = InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify
            (InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x) ^ 2 := by rw [hRep]
        _ = InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify
            ((InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.weylUpperMat x) ^ 2) := by
              rw [pow_two,
                ← InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify_mul,
                pow_two]
        _ = E 1 := by
          rw [hPauliSq,
            InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realify_one,
            map_one]
    let f : Tensor2 →ₐ[ℝ] Module.End ℝ KreinFrame4 :=
      doubleEndAlgHom.comp realTwoMatrixGradedTensorOnFourSpace.toAlgHom
    change f (realWeylUpperTensor x) * f (realWeylUpperTensor x) = 1
    calc
      _ = f (realWeylUpperTensor x * realWeylUpperTensor x) := by
        exact (f.map_mul _ _).symm
      _ = f (realWeylUpperTensor x ^ 2) := by rw [pow_two]
      _ = f 1 := by rw [hTensorSq]
      _ = 1 := f.map_one
  rw [hCreationSq, hWeylSq] at hSq
  exact zero_ne_one hSq

/-- The real Fock-matrix action agrees with the same operator on the doubled
Krein carrier. This transports the Hestenes representation to the owner used
for exterior creation, CAR, and Plücker readouts. -/
theorem hestenesEven_fock_action (x : HestenesEven) :
    fockMatrixToKreinOperator (hestenesEvenToFockMatrix x) =
        hestenesEvenOnDoubledKrein x := by
  calc
    fockMatrixToKreinOperator (hestenesEvenToFockMatrix x) =
        realThreeMatrixTensorOnH4 (hestenesEvenToThreeModeTensor x) := by
          simp [hestenesEvenToFockMatrix, fockMatrixToKreinOperator,
            fockMatrixToRealGradedTensor]
    _ = hestenesEvenOnDoubledKrein x := hestenesEven_threeMode_action x

/-- The operator representation retains the doubled real complex structure
as an endomorphism commuting with every represented even Hestenes element. -/
theorem hestenesEvenOnDoubledKrein_commutes_J (x : HestenesEven) :
    Commute (hestenesEvenOnDoubledKrein x)
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap := by
  change doubleEnd (realTwoMatrixGradedTensorOnFourSpace
      (hestenesEvenToRealGradedTensor x)) *
    InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap =
      InfoGeometry.Canonical.RealDoubledChiralKreinFrame.doubledComplexStructure.toLinearMap *
        doubleEnd (realTwoMatrixGradedTensorOnFourSpace
          (hestenesEvenToRealGradedTensor x))
  exact doubleEnd_commutes_with_hestenesJ _

/-- The representation is faithful: each arrow is an algebra equivalence or
an injective inclusion, so distinct real even Clifford elements remain
distinct in the graded tensor carrier. -/
theorem hestenesEvenToRealGradedTensor_injective :
    Function.Injective hestenesEvenToRealGradedTensor := by
  intro x y h
  have ht := congrArg twoMatrixGradedTensorMoritaEquiv h
  change twoMatrixGradedTensorMoritaEquiv
      (twoMatrixGradedTensorMoritaEquiv.symm
        (realNestedMatrixToFin4.symm
          (commutantToMatrix (realifyCommutantHom
            (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv x))))) =
    twoMatrixGradedTensorMoritaEquiv
      (twoMatrixGradedTensorMoritaEquiv.symm
        (realNestedMatrixToFin4.symm
          (commutantToMatrix (realifyCommutantHom
            (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv y))))) at ht
  simp only [twoMatrixGradedTensorMoritaEquiv.apply_symm_apply] at ht
  have h' := congrArg realNestedMatrixToFin4 ht
  change realNestedMatrixToFin4
      (realNestedMatrixToFin4.symm
        (commutantToMatrix (realifyCommutantHom
          (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv x)))) =
    realNestedMatrixToFin4
      (realNestedMatrixToFin4.symm
        (commutantToMatrix (realifyCommutantHom
          (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv y)))) at h'
  simp only [realNestedMatrixToFin4.apply_symm_apply] at h'
  have hm : realify (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv x) =
      realify (HestenesEvenPauliEquiv.clPlusPauliAlgEquiv y) := by
    simpa [commutantToMatrix, realifyCommutantHom, realifyRingHom] using h'
  exact HestenesEvenPauliEquiv.clPlusPauliAlgEquiv.injective
    (realifyCommutantAlgEquiv.injective (Subtype.ext hm))

/-- The doubled-Krein representation remains faithful because its final
diagonal lift is faithful. -/
theorem hestenesEvenOnDoubledKrein_injective :
    Function.Injective hestenesEvenOnDoubledKrein := by
  intro x y h
  apply hestenesEvenToRealGradedTensor_injective
  apply realTwoMatrixGradedTensorOnFourSpace.injective
  apply doubleEnd_injective
  exact h

/-- The three-mode extension is faithful because the existing two-mode
inclusion into the three-factor graded tensor is injective. -/
theorem hestenesEvenToThreeModeTensor_injective :
    Function.Injective hestenesEvenToThreeModeTensor := by
  intro x y h
  have h' : hestenesEvenToRealGradedTensor x =
      hestenesEvenToRealGradedTensor y := by
    apply twoModeIntoThreeMode_injective
    simpa [hestenesEvenToThreeModeTensor] using h
  exact hestenesEvenToRealGradedTensor_injective h'

/-- The real Fock-matrix realization is faithful as well: it is transported
through the existing algebra equivalence from the three-factor graded tensor. -/
theorem hestenesEvenToFockMatrix_injective :
    Function.Injective hestenesEvenToFockMatrix := by
  intro x y h
  apply hestenesEvenToThreeModeTensor_injective
  exact fockMatrixToRealGradedTensor.symm.injective h

end InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation
