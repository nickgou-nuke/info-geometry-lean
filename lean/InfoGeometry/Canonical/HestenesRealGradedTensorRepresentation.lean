/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesEvenPauliEquiv
import InfoGeometry.Canonical.Cl11JordanComplexCommutantEquiv
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge

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

/-- The real tensor representation, diagonally lifted to the doubled
Krein/Hestenes carrier. -/
def hestenesEvenOnDoubledKrein : HestenesEven →ₐ[ℝ]
    Module.End ℝ KreinFrame4 :=
  (doubleEndAlgHom.comp realTwoMatrixGradedTensorOnFourSpace.toAlgHom).comp
    hestenesEvenToRealGradedTensor

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
