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
import InfoGeometry.Canonical.RealSpacetime4x4Closure

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
open InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open scoped TensorProduct GradedTensorProduct

abbrev Tensor2 := InfoGeometry.Canonical.GradedTensorWeylBridge.twoMatrixGradedTensor
abbrev FourSpace := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace
abbrev KreinFrame4 := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4
abbrev RealSpacetime4x4 :=
  InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4

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

/-! ### Physical real spacetime momentum and the realification basis change

The complex Pauli source encodes real physical coordinates, while its real
matrix realification and the spacetime owner order the four real coordinates
differently. We record that change as an explicit index equivalence and prove
the matrix readout only after reindexing. -/

/-- The physical real spacetime vector encoded in the Pauli-source momentum
type. The resulting representation theorem below has real matrices as both
source and target. -/
def realSpacetimeFourMomentum (X : RealSpacetime4x4) :
    InfoGeometry.Physics.ChiralPoincareSouriauBridge.FourMomentum where
  E := (X.t : ℝ)
  px := (X.x : ℝ)
  py := (X.y : ℝ)
  pz := (X.z : ℝ)

/-- Realification orders coordinates as `(Re z₀, Re z₁, Im z₀, Im z₁)`,
whereas the Hestenes spacetime matrix uses `(Re z₀, Im z₀, Re z₁, Im z₁)`.
The swap of middle indices is the exact basis change. -/
def realPauliIndexEquiv : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

/-- The Pauli soldering of a physical real spacetime vector, realified and
reindexed into the Hestenes basis, is exactly the owner's real spacetime
matrix. -/
theorem realify_physicalPauliMomentum (X : RealSpacetime4x4) :
    Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realifyRingHom
          (InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum
            (realSpacetimeFourMomentum X))) =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X := by
  cases X with
  | mk t x y z =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.reindex_apply, realPauliIndexEquiv,
          Equiv.swap_apply_def, realifyRingHom_apply, realify_apply,
          blockRealify, realSpacetimeFourMomentum,
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum,
          InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix,
          finProdFinEquiv, Fin.divNat, Fin.modNat,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- The canonical real-coordinate super-Poincaré presentation has precisely
the physical Hestenes matrix as its reindexed real momentum readout. -/
theorem realSpacetimePresentation_momentum_readout
    (X : RealSpacetime4x4) :
    Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realifyRingHom
          ((realCoordinateSuperPoincarePresentation
            (realMinkowskiCircularCoordinate X)).Pspinor)) =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X := by
  have hWeyl :
      weylUpperMat
          (upperWeylCoordinate (realMinkowskiCircularCoordinate X)) =
        InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum
          (realSpacetimeFourMomentum X) := by
    cases X with
    | mk t x y z =>
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [weylUpperMat, upperWeylCoordinate,
            realMinkowskiCircularCoordinate, realSpacetimeFourMomentum,
            InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum,
            InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge.pauliSolder2x2,
            InfoGeometry.Quantum.PauliSoldering.solder,
            InfoGeometry.Quantum.PauliSoldering.σ0,
            InfoGeometry.Quantum.PauliSoldering.σ1,
            InfoGeometry.Quantum.PauliSoldering.σ2,
            InfoGeometry.Quantum.PauliSoldering.σ3] <;> ring
  rw [realCoordinatePresentation_solders_to_upperWeyl, hWeyl]
  exact realify_physicalPauliMomentum X

/-- In this canonical real-coordinate presentation, the realified odd-odd
supercharge relation reads as twice the physical Hestenes momentum matrix. -/
theorem realSpacetimePresentation_anticommutator_readout
    (X : RealSpacetime4x4) :
    Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realifyRingHom
          ((realCoordinateSuperPoincarePresentation
            (realMinkowskiCircularCoordinate X)).antiQQbar)) =
      (2 : ℝ) • InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix X := by
  rw [realify_superPoincare_relation]
  have hMomentum := realSpacetimePresentation_momentum_readout X
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hMomentum
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply] using
    congrArg (fun r : ℝ => (2 : ℝ) * r) hij

/-! ### Physical Rindler-plane Peirce supertranslations

The Peirce translation in the existing two-factor Koszul tensor is odd only
when its momentum matrix is checkerboard-even. Physical longitudinal
`(t,z)` momenta meet that condition. The following coordinate identification
connects their actual Peirce anticommutator readout to the existing
realified super-Poincaré momentum readout, without treating the stored
`ChiralOperatorPresentation` as a construction of supercharge operators. -/

/-- Embed the physical Rindler `(t,z)` plane into the existing real
`FourSpace` soldering coordinates `(t,z,x,y)`. -/
def realRindlerPlaneMomentum (X : RealSpacetime4x4) : FourSpace :=
  fourSpaceEquivVec22.symm (X.t, X.z, 0, 0)

/-- The upper Peirce translation is genuinely odd for longitudinal physical
momentum; the checkerboard condition follows from the diagonal soldering
matrix rather than being assumed. -/
theorem realRindlerPlaneTranslation_odd (X : RealSpacetime4x4) :
    translationInGradedTensor (realRindlerPlaneMomentum X) ∈
      twoMatrixProductGrading 1 := by
  rw [translationInGradedTensor_odd_iff]
  cases X with
  | mk t x y z =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [realRindlerPlaneMomentum, realMomentum,
          fourSpaceEquivVec22, InfoGeometry.Clifford.Soldering.soldering,
          InfoGeometry.Clifford.Soldering.sigma0,
          InfoGeometry.Clifford.Soldering.sigma1,
          InfoGeometry.Clifford.Soldering.sigma3,
          InfoGeometry.Clifford.Soldering.epsilon,
          matrixParity]

/-- The diagonal Peirce momentum for the Rindler plane, read in the
Hestenes four-coordinate matrix basis, is exactly the physical real
spacetime momentum matrix. The middle-index reordering is the already-owned
`realPauliIndexEquiv`. -/
theorem realRindlerPlanePeirceMomentum_readout (X : RealSpacetime4x4) :
    Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realNestedMatrixToFin4
          (diagonalMomentumOperator (realRindlerPlaneMomentum X))) =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix
        ⟨X.t, 0, 0, X.z⟩ := by
  cases X with
  | mk t x y z =>
      change Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
          (Matrix.reindex finProdFinEquiv finProdFinEquiv
            (fun a b : Fin 2 × Fin 2 =>
              diagonalMomentumOperator (realRindlerPlaneMomentum
                ⟨t, x, y, z⟩) a.1 b.1 a.2 b.2)) = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.reindex, Matrix.submatrix, realPauliIndexEquiv,
          Equiv.swap_apply_def,
          realRindlerPlaneMomentum, diagonalMomentumOperator,
          fourSpaceEquivVec22, realMomentum,
          InfoGeometry.Clifford.Soldering.soldering,
          InfoGeometry.Clifford.Soldering.sigma0,
          InfoGeometry.Clifford.Soldering.sigma1,
          InfoGeometry.Clifford.Soldering.sigma3,
          InfoGeometry.Clifford.Soldering.epsilon,
          InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix,
          finProdFinEquiv, Fin.divNat, Fin.modNat] <;> ring

/-- On the physical Rindler plane, the actual pair of odd Peirce charge
operators has real Hestenes matrix readout equal to the spacetime momentum.
This composes the genuine two-factor Koszul anticommutator with the existing
real soldering map; no complex-valued charge presentation is involved. -/
theorem realRindlerPlanePeirce_supercharge_anticommutator_readout
    (X : RealSpacetime4x4) :
    Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realNestedMatrixToFin4
          (twoMatrixGradedTensorMoritaEquiv
            (translationInGradedTensor (realRindlerPlaneMomentum X) *
                conjugatePeirceCharge +
              conjugatePeirceCharge *
                translationInGradedTensor (realRindlerPlaneMomentum X)))) =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix
        ⟨X.t, 0, 0, X.z⟩ := by
  have h : realNestedMatrixToFin4
      (twoMatrixGradedTensorMoritaEquiv
        (translationInGradedTensor (realRindlerPlaneMomentum X) *
            conjugatePeirceCharge +
          conjugatePeirceCharge *
            translationInGradedTensor (realRindlerPlaneMomentum X))) =
      realNestedMatrixToFin4
        (diagonalMomentumOperator (realRindlerPlaneMomentum X)) := by
    simpa only [AlgEquiv.apply_symm_apply] using
      congrArg
        (fun A => realNestedMatrixToFin4
          (twoMatrixGradedTensorMoritaEquiv A))
        (translationCharge_anticommutator_eq_diagonalMomentum
          (realRindlerPlaneMomentum X))
  rw [h]
  exact realRindlerPlanePeirceMomentum_readout X

/-- The `sqrt 2`-normalized Peirce translation and its complementary charge
are both odd in the real Koszul grading and satisfy the standard
`{Q, Q̄} = 2P` normalization on the physical longitudinal plane. Here the
charges are the existing Peirce operators themselves, scaled in the existing
real tensor algebra. -/
theorem realRindlerPlanePeirce_scaledCharges_odd_and_superPoincare
    (X : RealSpacetime4x4) :
    (Real.sqrt 2 • translationInGradedTensor (realRindlerPlaneMomentum X)) ∈
        twoMatrixProductGrading 1 ∧
      (Real.sqrt 2 • conjugatePeirceCharge) ∈ twoMatrixProductGrading 1 ∧
      (Real.sqrt 2 • translationInGradedTensor (realRindlerPlaneMomentum X)) *
          (Real.sqrt 2 • conjugatePeirceCharge) +
        (Real.sqrt 2 • conjugatePeirceCharge) *
          (Real.sqrt 2 • translationInGradedTensor (realRindlerPlaneMomentum X)) =
        (2 : ℝ) • twoMatrixGradedTensorMoritaEquiv.symm
          (diagonalMomentumOperator (realRindlerPlaneMomentum X)) := by
  refine ⟨?_, ?_, ?_⟩
  · change twoMatrixParity
        (Real.sqrt 2 • translationInGradedTensor (realRindlerPlaneMomentum X)) = _
    rw [map_smul, realRindlerPlaneTranslation_odd X, smul_neg]
  · change twoMatrixParity (Real.sqrt 2 • conjugatePeirceCharge) = _
    rw [map_smul, conjugatePeirceCharge_odd, smul_neg]
  have hsqrt : (Real.sqrt 2) * (Real.sqrt 2) = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  calc
    _ = ((Real.sqrt 2) * (Real.sqrt 2)) •
          (translationInGradedTensor (realRindlerPlaneMomentum X) *
            conjugatePeirceCharge +
           conjugatePeirceCharge *
            translationInGradedTensor (realRindlerPlaneMomentum X)) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          rw [smul_add]
    _ = (2 : ℝ) • twoMatrixGradedTensorMoritaEquiv.symm
          (diagonalMomentumOperator (realRindlerPlaneMomentum X)) := by
          rw [hsqrt, translationCharge_anticommutator_eq_diagonalMomentum]

/-- The normalized Peirce charges have exactly the same real matrix readout
as the odd-odd relation stored by the existing real-coordinate
Super-Poincaré presentation. The equality is after the established
reindexing into the Hestenes spacetime basis. -/
theorem realRindlerPlanePeirce_scaledCharges_readout_eq_superPoincare
    (X : RealSpacetime4x4) :
    Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realNestedMatrixToFin4
          (twoMatrixGradedTensorMoritaEquiv
            ((Real.sqrt 2 • translationInGradedTensor
                (realRindlerPlaneMomentum X)) *
                (Real.sqrt 2 • conjugatePeirceCharge) +
              (Real.sqrt 2 • conjugatePeirceCharge) *
                (Real.sqrt 2 • translationInGradedTensor
                  (realRindlerPlaneMomentum X))))) =
      Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realifyRingHom
          ((realCoordinateSuperPoincarePresentation
            (realMinkowskiCircularCoordinate
              ⟨X.t, 0, 0, X.z⟩)).antiQQbar)) := by
  have hcharges :=
    (realRindlerPlanePeirce_scaledCharges_odd_and_superPoincare X).2.2
  have hmatrix := congrArg
    (fun A : Tensor2 => Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
      (realNestedMatrixToFin4 (twoMatrixGradedTensorMoritaEquiv A))) hcharges
  calc
    _ = (2 : ℝ) • Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
          (realNestedMatrixToFin4
            (diagonalMomentumOperator (realRindlerPlaneMomentum X))) := by
          ext i j
          have hij := congrArg
            (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hmatrix
          simpa [Matrix.reindex_apply, Matrix.submatrix_apply,
            Matrix.smul_apply] using hij
    _ = (2 : ℝ) • InfoGeometry.Canonical.RealSpacetime4x4Closure.toMatrix
          ⟨X.t, 0, 0, X.z⟩ := by rw [realRindlerPlanePeirceMomentum_readout]
    _ = Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
          (realifyRingHom
            ((realCoordinateSuperPoincarePresentation
              (realMinkowskiCircularCoordinate
                ⟨X.t, 0, 0, X.z⟩)).antiQQbar)) :=
          (realSpacetimePresentation_anticommutator_readout _).symm

/-- The Peirce translation/charge anticommutator is the momentum operator
`P`, whereas the stored Super-Poincaré odd-odd relation is normalized as
`2P`. On the physical longitudinal plane their real matrix readouts therefore
agree after the exact factor `1/2`; this compares the two owner constructions
without asserting a termwise identification of their charges. -/
theorem realRindlerPlanePeirce_readout_eq_half_superPoincare_anticommutator
    (X : RealSpacetime4x4) :
    Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
        (realNestedMatrixToFin4
          (twoMatrixGradedTensorMoritaEquiv
            (translationInGradedTensor (realRindlerPlaneMomentum X) *
                conjugatePeirceCharge +
              conjugatePeirceCharge *
                translationInGradedTensor (realRindlerPlaneMomentum X)))) =
      (1 / 2 : ℝ) •
        Matrix.reindex realPauliIndexEquiv realPauliIndexEquiv
          (realifyRingHom
            ((realCoordinateSuperPoincarePresentation
              (realMinkowskiCircularCoordinate
                ⟨X.t, 0, 0, X.z⟩)).antiQQbar)) := by
  rw [realRindlerPlanePeirce_supercharge_anticommutator_readout,
    realSpacetimePresentation_anticommutator_readout]
  simp [RealSpacetime4x4Closure.toMatrix]

/-- On the longitudinal Rindler plane, the determinant of the real Peirce
momentum coefficient is the physical Minkowski interval. The general
`(2,2)` soldering determinant is restricted here to the `(t,z)` subspace, so
the other two coordinates vanish. -/
theorem realRindlerPlanePeirce_determinant_eq_interval
    (X : RealSpacetime4x4) :
    (translationBlock (realRindlerPlaneMomentum X) 0 1).det =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
        ⟨X.t, 0, 0, X.z⟩ := by
  rw [translationBlock_det]
  simp [realRindlerPlaneMomentum,
    InfoGeometry.Canonical.RealSolderingWeylKreinBridge.fourSpaceEquivVec22,
    InfoGeometry.Clifford.Soldering.q22,
    InfoGeometry.Canonical.RealSpacetime4x4Closure.interval]

/-- The Peirce momentum determinant and the three-mode Majorana CAR square
are the same scalar on the doubled Krein carrier. -/
theorem realRindlerPlanePeirce_determinant_eq_majorana_square
    (X : RealSpacetime4x4) :
    (translationBlock (realRindlerPlaneMomentum X) 0 1).det •
        (1 : Module.End ℝ KreinFrame4) =
      realThreeMatrixTensorOnH4
        (realMinkowskiMajorana ⟨X.t, 0, 0, X.z⟩) *
        realThreeMatrixTensorOnH4
          (realMinkowskiMajorana ⟨X.t, 0, 0, X.z⟩) := by
  rw [realMinkowskiMajorana_onKrein_square,
    ← realRindlerPlanePeirce_determinant_eq_interval]

/-- The determinant readout of the real Peirce supertranslation is invariant
under the existing Souriau/Lipschitz Rindler boost. -/
theorem realRindlerPlanePeirce_determinant_rindler_invariant
    (X : RealSpacetime4x4) (s : ℝ) :
    (translationBlock
        (realRindlerPlaneMomentum
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s))
        0 1).det =
      (translationBlock (realRindlerPlaneMomentum X) 0 1).det := by
  have hplane :
      (⟨(InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).t,
        0, 0,
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).z⟩ :
          RealSpacetime4x4) =
        InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost
          ⟨X.t, 0, 0, X.z⟩ s := by
    cases X
    rfl
  calc
    _ = InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
        ⟨(InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).t,
          0, 0,
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s).z⟩ :=
          realRindlerPlanePeirce_determinant_eq_interval _
    _ = InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost
          ⟨X.t, 0, 0, X.z⟩ s) := by rw [← hplane]
    _ = InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
        ⟨X.t, 0, 0, X.z⟩ :=
      InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_flow_isometry _ s
    _ = _ := (realRindlerPlanePeirce_determinant_eq_interval X).symm

end InfoGeometry.Canonical.RealSuperPoincareGradedTensorBridge
