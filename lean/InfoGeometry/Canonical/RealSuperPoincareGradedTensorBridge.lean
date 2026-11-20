/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CuntzDeformedSuperPoincare
import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge

/-!
# Real graded-tensor realization of the operator super-Poincaré relation

The source operator presentation stores its spinor matrices over `ℂ`. This
module transports those matrices through the existing realification with its
real complex-structure operator, then through the genuine Koszul-graded
`M₂(ℝ) ᵍ⊗ M₂(ℝ)` equivalence and onto the real doubled Krein carrier. The
result is a real operator equation. It does not claim that a spinor matrix
alone constructs a spacetime translation action or a Lorentz representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealSuperPoincareGradedTensorBridge

open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Canonical.GradedTensorWeylBridge
open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Physics.CuntzDeformedSuperPoincare
open InfoGeometry.Canonical.HestenesRealGradedTensorRepresentation
open InfoGeometry.Canonical.RealChiralCARTranslationSynthesis
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open scoped TensorProduct GradedTensorProduct

abbrev Tensor2 := InfoGeometry.Canonical.GradedTensorWeylBridge.twoMatrixGradedTensor
abbrev FourSpace := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace
abbrev KreinFrame4 := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4

/-- Real matrix on the Koszul-graded tensor carrier corresponding to a
spinor operator matrix. -/
def chiralOperatorToRealGradedTensor (A : M2C) : Tensor2 :=
  twoMatrixGradedTensorMoritaEquiv.symm
    (realNestedMatrixToFin4.symm (realifyRingHom A))

/-- The corresponding real endomorphism on the two-sheeted four-dimensional
real carrier. -/
def chiralOperatorOnFourSpace (A : M2C) : Module.End ℝ FourSpace :=
  realTwoMatrixGradedTensorOnFourSpace (chiralOperatorToRealGradedTensor A)

/-- Diagonal lift of the real spinor operator to the doubled Krein carrier. -/
def chiralOperatorOnDoubledKrein (A : M2C) : Module.End ℝ KreinFrame4 :=
  doubleEnd (chiralOperatorOnFourSpace A)

/-- The operator-valued super-Poincaré equation survives realification at
the matrix level, with real scalar `2`. -/
theorem realify_superPoincare_relation (S : ChiralOperatorPresentation) :
    realifyRingHom S.antiQQbar = (2 : ℝ) • realifyRingHom S.Pspinor := by
  have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [S.super_poincare, htwo]
  exact realify_real_smul 2 S.Pspinor

/-- The super-Poincaré relation in the genuine two-factor real graded
tensor representation. -/
theorem realGradedTensor_superPoincare_relation
    (S : ChiralOperatorPresentation) :
    chiralOperatorToRealGradedTensor S.antiQQbar =
      (2 : ℝ) • chiralOperatorToRealGradedTensor S.Pspinor := by
  have h := congrArg
    (fun A : Mat4R => twoMatrixGradedTensorMoritaEquiv.symm
      (realNestedMatrixToFin4.symm A))
    (realify_superPoincare_relation S)
  simpa [chiralOperatorToRealGradedTensor, map_smul] using h

/-- If the spinor momentum in a `ChiralOperatorPresentation` is the circular
upper Weyl channel, its real graded-tensor realization is the image of the
corresponding real Hestenes-even element. This identifies the channel
operator on the actual two-factor Koszul tensor; it does not assert that an
arbitrary complex spinor presentation has real coefficients. -/
theorem chiralOperatorToRealGradedTensor_eq_hestenesEven
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate)
    (S : ChiralOperatorPresentation)
    (hP : S.Pspinor = weylUpperMat x) :
    chiralOperatorToRealGradedTensor S.Pspinor =
      hestenesEvenToRealGradedTensor (circularWeylUpperEven x) := by
  rw [hP]
  change
    twoMatrixGradedTensorMoritaEquiv.symm
        (realNestedMatrixToFin4.symm
          (InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.realifyRingHom
            (weylUpperMat x))) =
      hestenesEvenToRealGradedTensor (circularWeylUpperEven x)
  rw [← circularWeylUpperTensor_eq_hestenesEven_image]
  apply twoMatrixGradedTensorMoritaEquiv.injective
  apply realNestedMatrixToFin4.injective
  simp only [AlgEquiv.apply_symm_apply]
  rw [realWeylUpperTensor_represents_weylUpperMat]
  rfl

/-- The same conditional Weyl/Hestenes identification after the existing
real graded-tensor action on the doubled Krein carrier. -/
theorem chiralOperatorOnDoubledKrein_eq_hestenesEvenOnDoubledKrein
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate)
    (S : ChiralOperatorPresentation)
    (hP : S.Pspinor = weylUpperMat x) :
    chiralOperatorOnDoubledKrein S.Pspinor =
      hestenesEvenOnDoubledKrein (circularWeylUpperEven x) := by
  have h := congrArg
    (fun A : Tensor2 =>
      doubleEnd (realTwoMatrixGradedTensorOnFourSpace A))
    (chiralOperatorToRealGradedTensor_eq_hestenesEven x S hP)
  simpa [chiralOperatorOnDoubledKrein, chiralOperatorOnFourSpace,
    hestenesEvenOnDoubledKrein, doubleEndAlgHom] using h

/-- The same operator equation acts on the real `FourSpace` carrier. -/
theorem fourSpace_superPoincare_relation
    (S : ChiralOperatorPresentation) :
    chiralOperatorOnFourSpace S.antiQQbar =
      (2 : ℝ) • chiralOperatorOnFourSpace S.Pspinor := by
  have h := congrArg realTwoMatrixGradedTensorOnFourSpace
    (realGradedTensor_superPoincare_relation S)
  simpa [chiralOperatorOnFourSpace, map_smul] using h

/-- The real spinor-momentum relation transported to the doubled Krein
carrier. -/
theorem doubledKrein_superPoincare_relation
    (S : ChiralOperatorPresentation) :
    chiralOperatorOnDoubledKrein S.antiQQbar =
      (2 : ℝ) • chiralOperatorOnDoubledKrein S.Pspinor := by
  have h := congrArg doubleEndAlgHom (fourSpace_superPoincare_relation S)
  simpa [chiralOperatorOnDoubledKrein, doubleEndAlgHom] using h

/-- Under the explicit circular-Weyl identification of the spinor momentum,
the transported super-Poincaré anticommutator is twice the corresponding
real Hestenes-even operator on the doubled Krein carrier. -/
theorem doubledKrein_superPoincare_eq_two_hestenesEven
    (x : InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate)
    (S : ChiralOperatorPresentation)
    (hP : S.Pspinor = weylUpperMat x) :
    chiralOperatorOnDoubledKrein S.antiQQbar =
      (2 : ℝ) • hestenesEvenOnDoubledKrein (circularWeylUpperEven x) := by
  rw [doubledKrein_superPoincare_relation,
    chiralOperatorOnDoubledKrein_eq_hestenesEvenOnDoubledKrein x S hP]

/-- The real four-vector represented by an upper circular coordinate block.
The remaining four coordinates belong to the independent lower sheet and
are set to zero here. -/
def upperWeylCoordinate (x : Coordinate) : Coordinate :=
  fun i => if i.val < 4 then x i else 0

/-- The owner `FourMomentum` is complex-valued. This constructor embeds a
real Weyl four-vector using `Complex.ofReal`; the Clifford and graded-tensor
carriers in the resulting theorem remain real. -/
def realFourMomentumOfCoordinate (x : Coordinate) :
    InfoGeometry.Physics.ChiralPoincareSouriauBridge.FourMomentum where
  E := (x 0 : ℝ)
  px := (x 1 : ℝ)
  py := (x 2 : ℝ)
  pz := (x 3 : ℝ)

/-- A canonical stored super-Poincaré presentation sourced from real
four-coordinate data. This packages the Pauli-soldered momentum identity;
it does not construct supercharge operators. -/
def realCoordinateSuperPoincarePresentation (x : Coordinate) :
    ChiralOperatorPresentation where
  antiQQbar := (2 : ℂ) • InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum
    (realFourMomentumOfCoordinate x)
  Pspinor := InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum
    (realFourMomentumOfCoordinate x)
  super_poincare := by
    ext i j
    simp

/-- The real-coordinate sourced presentation agrees with the circular upper
Weyl soldering matrix. This is the precise point where the existing complex
Pauli presentation is realized from real data. -/
theorem realCoordinatePresentation_solders_to_upperWeyl (x : Coordinate) :
    (realCoordinateSuperPoincarePresentation x).Pspinor =
      weylUpperMat (upperWeylCoordinate x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCoordinateSuperPoincarePresentation, realFourMomentumOfCoordinate,
    InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum,
    weylUpperMat, upperWeylCoordinate,
    InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge.pauliSolder2x2,
    InfoGeometry.Quantum.PauliSoldering.solder,
    InfoGeometry.Quantum.PauliSoldering.σ0,
    InfoGeometry.Quantum.PauliSoldering.σ1,
    InfoGeometry.Quantum.PauliSoldering.σ2,
    InfoGeometry.Quantum.PauliSoldering.σ3] <;> ring

/-- An unconditional real graded-tensor/Hestenes bridge for the canonical
real-coordinate super-Poincaré presentation. The operator equality is in the
actual two-factor Koszul tensor of real `2 × 2` matrices. -/
theorem realCoordinatePresentation_superPoincare_eq_two_hestenesEven
    (x : Coordinate) :
    chiralOperatorOnDoubledKrein
        (realCoordinateSuperPoincarePresentation x).antiQQbar =
      (2 : ℝ) • hestenesEvenOnDoubledKrein
        (circularWeylUpperEven (upperWeylCoordinate x)) := by
  apply doubledKrein_superPoincare_eq_two_hestenesEven
  exact realCoordinatePresentation_solders_to_upperWeyl x

end InfoGeometry.Canonical.RealSuperPoincareGradedTensorBridge
