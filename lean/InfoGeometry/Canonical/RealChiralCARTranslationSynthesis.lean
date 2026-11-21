/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.RealGradedZornCARBridge
import InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
import InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge
import InfoGeometry.Canonical.SouriauKillingLipschitzBridge
import InfoGeometry.Algebra.ChiralRealHyperbolicRotor
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import InfoGeometry.Clifford.Cl33FiniteJWMajoranaMatrix
import InfoGeometry.Quantum.Realification
import InfoGeometry.Quantum.RealificationCategory
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.Projective.ExteriorPowerPluckerBridge

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
open InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge
open InfoGeometry.Canonical.SouriauKillingLipschitzBridge
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

/-! ### Rindler flow transported to the real Majorana Clifford contraction

The Rindler boost is already an isometry of physical real `(1,3)` spacetime,
and the Majorana contraction already represents the corresponding quadratic
form in the genuine three-factor real Koszul tensor. The following bridge
states the resulting operator-level invariant. It asserts equality of
quadratic contractions, not equality of the underlying Clifford vectors. -/

/-- The real Majorana contraction of a Rindler-boosted Minkowski vector has
the same square as the contraction before the boost. This joins the physical
Rindler flow to the actual three-mode real graded-matrix carrier. -/
theorem realMinkowskiMajorana_rindlerBoost_square
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (s : ℝ) :
    realMinkowskiMajorana
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) ^ 2 =
      realMinkowskiMajorana X ^ 2 := by
  calc
    realMinkowskiMajorana
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) ^ 2 =
        InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) •
            (1 : realThreeMatrixGradedTensor) := by
          simpa [pow_two] using realMinkowskiMajorana_square
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s)
    _ = InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X •
          (1 : realThreeMatrixGradedTensor) := by
          exact congrArg
            (fun r : ℝ => r • (1 : realThreeMatrixGradedTensor))
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_flow_isometry X s)
    _ = realMinkowskiMajorana X ^ 2 := by
          simpa [pow_two] using (realMinkowskiMajorana_square X).symm

/-! ### Infinitesimal spin lift on the real Majorana CAR algebra

The preceding result only used the quadratic form.  The real CAR owner also
contains the four Clifford generators themselves, so the longitudinal
Rindler Killing generator can be represented by their bivector commutator.
This is the finite-dimensional algebraic spin lift; it makes no claim about
a covariant derivative or a curved-spacetime spinor bundle. -/

/-- The real bivector in the longitudinal time/space plane of the CAR
representation. -/
def rindlerMajoranaBivector : realThreeMatrixGradedTensor :=
  realMajoranaTimeHead * realMajoranaSpaceTail

/-- The Rindler CAR bivector is the image of the corresponding native
`(+---)` Hestenes bivector under the existing real Clifford representation.
This identifies the actual generator on the graded CAR carrier with
`-(1/2) γ₀γ₃` in `Cl(1,3)`; it is not an abstract spinor-action wrapper. -/
theorem rindlerMajoranaBivector_eq_hestenes_image :
    rindlerMajoranaBivector =
      realMajoranaCliffordRep
        (HestenesCl14.gamma 0 * HestenesCl14.gamma 3) := by
  rw [rindlerMajoranaBivector, map_mul,
    realMajoranaCliffordRep_gamma, realMajoranaCliffordRep_gamma]
  simp [realMajoranaVectorRep,
    InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge.v14ToRealSpacetime,
    InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge.realMinkowskiMajorana,
    HestenesCl14.basisVec]

/-- The physical Rindler `(t,z)` plane is a quadratic subspace of the
repository's native real `(+---)` spacetime carrier. The coordinates retain
the established time/space convention. -/
def rindlerPlaneToV14 : InfoGeometry.Clifford.Cl11Matrix.Vec11 →ₗ[ℝ]
    HestenesCl14.V14 where
  toFun v := fun i => if i = 0 then v.1 else if i = 3 then v.2 else 0
  map_add' v w := by
    ext i
    fin_cases i <;> simp
  map_smul' r v := by
    ext i
    fin_cases i <;> simp [smul_eq_mul]

/-- The embedding of the Rindler plane preserves the actual quadratic forms
`q11` and `Q14`; hence its Clifford lift uses the native universal property. -/
theorem rindlerPlaneToV14_preserves_quadraticForm
    (v : InfoGeometry.Clifford.Cl11Matrix.Vec11) :
    HestenesCl14.Q14 (rindlerPlaneToV14 v) =
      InfoGeometry.Clifford.Cl11Matrix.q11 v := by
  rw [HestenesCl14.Q14_apply,
    InfoGeometry.Clifford.Cl11Matrix.q11_apply]
  simp [rindlerPlaneToV14, HestenesCl14.qCoeff,
    Fin.sum_univ_four]
  ring

/-- The genuine algebra homomorphism from the Rindler `Cl(1,1)` plane into
the existing real spacetime `Cl(1,3)` carrier. -/
def rindlerPlaneCliffordToCl14 :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 →ₐ[ℝ]
      HestenesCl14.Cl14 :=
  CliffordAlgebra.lift InfoGeometry.Clifford.Cl11Matrix.q11
    ⟨HestenesCl14.ι14.comp rindlerPlaneToV14, by
      intro v
      change HestenesCl14.ι14 (rindlerPlaneToV14 v) *
          HestenesCl14.ι14 (rindlerPlaneToV14 v) =
        algebraMap ℝ HestenesCl14.Cl14
          (InfoGeometry.Clifford.Cl11Matrix.q11 v)
      rw [CliffordAlgebra.ι_sq_scalar,
        rindlerPlaneToV14_preserves_quadraticForm]⟩

@[simp] theorem rindlerPlaneCliffordToCl14_timeGenerator :
    rindlerPlaneCliffordToCl14
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) =
      HestenesCl14.gamma 0 := by
  rw [rindlerPlaneCliffordToCl14, CliffordAlgebra.lift_ι_apply,
    LinearMap.comp_apply]
  congr 1
  ext i
  fin_cases i <;> simp [rindlerPlaneToV14, HestenesCl14.basisVec]

@[simp] theorem rindlerPlaneCliffordToCl14_spaceGenerator :
    rindlerPlaneCliffordToCl14
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)) =
      HestenesCl14.gamma 3 := by
  rw [rindlerPlaneCliffordToCl14, CliffordAlgebra.lift_ι_apply,
    LinearMap.comp_apply]
  congr 1
  ext i
  fin_cases i <;> simp [rindlerPlaneToV14, HestenesCl14.basisVec]

/-- Composing the native plane embedding with the existing real Majorana
representation gives an algebra homomorphism directly into the three-mode
Koszul-graded CAR carrier. -/
def rindlerPlaneCliffordToCAR :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 →ₐ[ℝ]
      realThreeMatrixGradedTensor :=
  realMajoranaCliffordRep.comp rindlerPlaneCliffordToCl14

@[simp] theorem rindlerPlaneCliffordToCAR_timeGenerator :
    rindlerPlaneCliffordToCAR
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) =
      realMajoranaTimeHead := by
  rw [rindlerPlaneCliffordToCAR, AlgHom.comp_apply,
    rindlerPlaneCliffordToCl14_timeGenerator,
    realMajoranaCliffordRep_gamma]
  simp [realMajoranaVectorRep,
    InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge.v14ToRealSpacetime,
    InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge.realMinkowskiMajorana,
    HestenesCl14.basisVec]

@[simp] theorem rindlerPlaneCliffordToCAR_spaceGenerator :
    rindlerPlaneCliffordToCAR
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1)) =
      realMajoranaSpaceTail := by
  rw [rindlerPlaneCliffordToCAR, AlgHom.comp_apply,
    rindlerPlaneCliffordToCl14_spaceGenerator,
    realMajoranaCliffordRep_gamma]
  simp [realMajoranaVectorRep,
    InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge.v14ToRealSpacetime,
    InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge.realMinkowskiMajorana,
    HestenesCl14.basisVec]

/-- The plane Clifford embedding sends the native `Cl(1,1)` boost bivector to
the actual longitudinal bivector in the real CAR algebra. -/
@[simp] theorem rindlerPlaneCliffordToCAR_bivector :
    rindlerPlaneCliffordToCAR
        (InfoGeometry.Clifford.Cl11Matrix.J1_cl) =
      rindlerMajoranaBivector := by
  rw [rindlerPlaneCliffordToCAR, AlgHom.comp_apply,
    show InfoGeometry.Clifford.Cl11Matrix.J1_cl =
      CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0) *
        CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1) from rfl,
    map_mul, rindlerPlaneCliffordToCl14_timeGenerator,
    rindlerPlaneCliffordToCl14_spaceGenerator]
  exact rindlerMajoranaBivector_eq_hestenes_image.symm

/-- The bivector implementing the infinitesimal boost in the real
three-mode Koszul-graded CAR algebra. The sign is chosen so its commutator
acts by `t ↦ z`, `z ↦ t`, matching the owner's Rindler convention. -/
def rindlerMajoranaSpinGenerator : realThreeMatrixGradedTensor :=
  (- (1 / 2 : ℝ)) • rindlerMajoranaBivector

/-- The infinitesimal Rindler spin generator in the real CAR algebra is the
image of the existing `Cl(1,1)` bivector generator under the quadratic-plane
embedding. Its normalization agrees with Souriau's finite matrix Kosmann
correction owner, which uses the contracted bivector `2 * J1`. -/
theorem rindlerMajoranaSpinGenerator_eq_embeddedKosmannGenerator :
    rindlerMajoranaSpinGenerator =
      rindlerPlaneCliffordToCAR
        ((- (1 / 2 : ℝ)) • InfoGeometry.Clifford.Cl11Matrix.J1_cl) := by
  rw [rindlerMajoranaSpinGenerator, map_smul,
    rindlerPlaneCliffordToCAR_bivector]

/-- The finite real Kosmann correction in the Souriau Rindler owner acts on
the `Cl(1,1)` matrix spinor by left multiplication. Transporting that actual
spinor through the existing quadratic-plane Clifford representation gives
left multiplication by the real three-mode CAR boost generator. This fixes
the generator and spinor action together; it does not promote the finite
matrix correction to a curved spinor-bundle Lie derivative. -/
theorem kosmannCorrection_transports_to_realCAR (ψ :
    InfoGeometry.Clifford.Cl11Matrix.Mat2) :
    rindlerPlaneCliffordToCAR
        (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm
          (InfoGeometry.Canonical.SouriauKillingLipschitzBridge.kosmannCorrection
            ((2 : ℝ) • InfoGeometry.Clifford.Cl11Matrix.J1) ψ)) =
      rindlerMajoranaSpinGenerator *
        rindlerPlaneCliffordToCAR
          (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm ψ) := by
  rw [InfoGeometry.Canonical.SouriauKillingLipschitzBridge.kosmannCorrection_rindler_generator]
  have hJ : InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm
      InfoGeometry.Clifford.Cl11Matrix.J1 =
        InfoGeometry.Clifford.Cl11Matrix.J1_cl := by
    apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
    have hJmap : InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        InfoGeometry.Clifford.Cl11Matrix.J1_cl =
          InfoGeometry.Clifford.Cl11Matrix.J1 := by
      rw [show InfoGeometry.Clifford.Cl11Matrix.J1_cl =
          CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0) *
            CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1) from rfl,
        map_mul,
        InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_pos,
        InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_neg,
        InfoGeometry.Clifford.Cl11Matrix.Eplus_mul_Eminus]
    rw [InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.apply_symm_apply]
    exact hJmap.symm
  calc
    _ = rindlerPlaneCliffordToCAR
        (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm
          (((- (1 / 2 : ℝ)) • InfoGeometry.Clifford.Cl11Matrix.J1) * ψ)) := by
            simp only [neg_smul]
    _ = rindlerPlaneCliffordToCAR
        (((- (1 / 2 : ℝ)) • InfoGeometry.Clifford.Cl11Matrix.J1_cl) *
          InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm ψ) := by
            simp only [map_mul, map_smul, hJ]
    _ = rindlerPlaneCliffordToCAR
          ((- (1 / 2 : ℝ)) • InfoGeometry.Clifford.Cl11Matrix.J1_cl) *
        rindlerPlaneCliffordToCAR
          (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm ψ) := map_mul _ _ _
    _ = _ := by
      rw [← rindlerMajoranaSpinGenerator_eq_embeddedKosmannGenerator]

/-- The infinitesimal real CAR boost generator is precisely the represented
Hestenes bivector with the standard half-angle normalization. -/
theorem rindlerMajoranaSpinGenerator_eq_hestenes_image :
    rindlerMajoranaSpinGenerator =
      realMajoranaCliffordRep
        ((- (1 / 2 : ℝ)) •
          (HestenesCl14.gamma 0 * HestenesCl14.gamma 3)) := by
  rw [rindlerMajoranaSpinGenerator, rindlerMajoranaBivector_eq_hestenes_image,
    map_smul]

/-- The finite real hyperbolic spin rotor for rapidity `s` in the Rindler
plane. Its coefficients are real cosh/sinh functions and its generator is
the existing CAR bivector. -/
def rindlerMajoranaSpinRotor (s : ℝ) : realThreeMatrixGradedTensor :=
  Real.cosh (s / 2) • (1 : realThreeMatrixGradedTensor) -
    Real.sinh (s / 2) • rindlerMajoranaBivector

/-- Reverse rotor, obtained by changing the sign of the bivector term. -/
def rindlerMajoranaSpinRotorReverse (s : ℝ) : realThreeMatrixGradedTensor :=
  Real.cosh (s / 2) • (1 : realThreeMatrixGradedTensor) +
    Real.sinh (s / 2) • rindlerMajoranaBivector

/-- The finite Souriau/Lipschitz boost rotor, transported through the
quadratic-plane Clifford embedding, is exactly the real Majorana CAR rotor.
This identifies the algebra element, not only its induced vector action. -/
theorem rindlerMajoranaRotor_eq_souriauBoostRotor (s : ℝ) :
    rindlerPlaneCliffordToCAR
        (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm
          (InfoGeometry.Canonical.SouriauKillingLipschitzBridge.boostRotor s)) =
      rindlerMajoranaSpinRotor s := by
  rw [InfoGeometry.Canonical.SouriauKillingLipschitzBridge.boostRotor_eq_cl11SpinRotorReverse,
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm_apply_apply,
    InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor_reverse]
  simp only [map_sub, map_smul, map_one, rindlerPlaneCliffordToCAR_bivector]
  rfl

private lemma commutator_add_real_tensor
    (A B C : realThreeMatrixGradedTensor) :
    A * (B + C) - (B + C) * A = (A * B - B * A) + (A * C - C * A) := by
  noncomm_ring

private lemma commutator_left_add_real_tensor
    (A B C : realThreeMatrixGradedTensor) :
    (A + B) * C - C * (A + B) =
      (A * C - C * A) + (B * C - C * B) := by
  noncomm_ring

private lemma commutator_smul_real_tensor
    (r : ℝ) (A B : realThreeMatrixGradedTensor) :
    A * (r • B) - (r • B) * A = r • (A * B - B * A) := by
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]

private lemma commutator_left_smul_real_tensor
    (r : ℝ) (A B : realThreeMatrixGradedTensor) :
    (r • A) * B - B * (r • A) = r • (A * B - B * A) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]

/-- The commutator with the Rindler bivector sends the time Majorana to the
longitudinal space Majorana and the longitudinal space Majorana to the time
Majorana. -/
private theorem rindlerBivector_commutators :
    let γt := realMajoranaTimeHead
    let γz := realMajoranaSpaceTail
    let B := γt * γz
    B * γt - γt * B = -(2 : ℝ) • γz ∧
      B * γz - γz * B = -(2 : ℝ) • γt ∧
      B * realMajoranaSpaceHead - realMajoranaSpaceHead * B = 0 ∧
      B * realMajoranaSpaceMiddle - realMajoranaSpaceMiddle * B = 0 := by
  dsimp
  have ht2 : realMajoranaTimeHead * realMajoranaTimeHead = 1 :=
    realMajorana_minkowski_diagonal_squares.1
  have hz2 : realMajoranaSpaceTail * realMajoranaSpaceTail = -1 :=
    realMajorana_minkowski_diagonal_squares.2.2.2
  have htz := realMajoranaHead_tail_cross_anticommutators.2.1
  have htx := realMajoranaHead_middle_cross_anticommutators.1
  have htzx := realMajoranaHead_tail_cross_anticommutators.2.2.2
  have hHeadX := realMajoranaHead_splitClifford_relations.2.2
  have htzm := realMajoranaSpaceMiddle_spaceTail_anticommute
  have hzt : realMajoranaSpaceTail * realMajoranaTimeHead =
      -(realMajoranaTimeHead * realMajoranaSpaceTail) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using htz)
  have hxt : realMajoranaSpaceHead * realMajoranaTimeHead =
      -(realMajoranaTimeHead * realMajoranaSpaceHead) := by
    exact eq_neg_of_add_eq_zero_left
      (by simpa [add_comm] using hHeadX)
  have htx' : realMajoranaTimeHead * realMajoranaSpaceHead =
      -(realMajoranaSpaceHead * realMajoranaTimeHead) :=
    eq_neg_of_add_eq_zero_left hHeadX
  have hxz : realMajoranaSpaceTail * realMajoranaSpaceHead =
      -(realMajoranaSpaceHead * realMajoranaSpaceTail) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using htzx)
  have hymt : realMajoranaSpaceMiddle * realMajoranaTimeHead =
      -(realMajoranaTimeHead * realMajoranaSpaceMiddle) := by
    exact eq_neg_of_add_eq_zero_left
      (by simpa [add_comm] using htx)
  have htym' : realMajoranaTimeHead * realMajoranaSpaceMiddle =
      -(realMajoranaSpaceMiddle * realMajoranaTimeHead) :=
    eq_neg_of_add_eq_zero_left htx
  have hymz : realMajoranaSpaceTail * realMajoranaSpaceMiddle =
      -(realMajoranaSpaceMiddle * realMajoranaSpaceTail) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using htzm)
  have hT :
      (realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaTimeHead -
        realMajoranaTimeHead *
          (realMajoranaTimeHead * realMajoranaSpaceTail) =
        -(2 : ℝ) • realMajoranaSpaceTail := by
    calc
      _ = realMajoranaTimeHead *
            (realMajoranaSpaceTail * realMajoranaTimeHead) -
          (realMajoranaTimeHead * realMajoranaTimeHead) *
            realMajoranaSpaceTail := by noncomm_ring
      _ = realMajoranaTimeHead *
            (-(realMajoranaTimeHead * realMajoranaSpaceTail)) -
          1 * realMajoranaSpaceTail := by rw [hzt, ht2]
      _ = -realMajoranaSpaceTail - realMajoranaSpaceTail := by
          simp only [mul_neg, one_mul]
          rw [← mul_assoc, ht2]
          simp
      _ = -(2 : ℝ) • realMajoranaSpaceTail := by
          module
  have hZ :
      (realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaSpaceTail -
        realMajoranaSpaceTail *
          (realMajoranaTimeHead * realMajoranaSpaceTail) =
        -(2 : ℝ) • realMajoranaTimeHead := by
    calc
      _ = realMajoranaTimeHead *
            (realMajoranaSpaceTail * realMajoranaSpaceTail) -
          (realMajoranaSpaceTail * realMajoranaTimeHead) *
            realMajoranaSpaceTail := by noncomm_ring
      _ = realMajoranaTimeHead * (-1) -
          (-(realMajoranaTimeHead * realMajoranaSpaceTail)) *
            realMajoranaSpaceTail := by rw [hz2, hzt]
      _ = -realMajoranaTimeHead +
            (realMajoranaTimeHead * realMajoranaSpaceTail) *
              realMajoranaSpaceTail := by simp
      _ = -realMajoranaTimeHead +
            realMajoranaTimeHead *
              (realMajoranaSpaceTail * realMajoranaSpaceTail) := by rw [mul_assoc]
      _ = -realMajoranaTimeHead - realMajoranaTimeHead := by
          rw [hz2]
          simp [mul_neg, mul_one]; abel
      _ = -(2 : ℝ) • realMajoranaTimeHead := by
          module
  have hBX :
      (realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaSpaceHead =
        realMajoranaSpaceHead *
          (realMajoranaTimeHead * realMajoranaSpaceTail) := by
    calc
      _ = realMajoranaTimeHead *
            (realMajoranaSpaceTail * realMajoranaSpaceHead) := by rw [mul_assoc]
      _ = realMajoranaTimeHead *
            (-(realMajoranaSpaceHead * realMajoranaSpaceTail)) := by rw [hxz]
      _ = -((realMajoranaTimeHead * realMajoranaSpaceHead) *
            realMajoranaSpaceTail) := by noncomm_ring
      _ = -((-(realMajoranaSpaceHead * realMajoranaTimeHead)) *
            realMajoranaSpaceTail) := by rw [htx']
      _ = (realMajoranaSpaceHead * realMajoranaTimeHead) *
            realMajoranaSpaceTail := by simp only [neg_mul, neg_neg]
      _ = realMajoranaSpaceHead *
            (realMajoranaTimeHead * realMajoranaSpaceTail) := by rw [← mul_assoc]
  have hBY :
      (realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaSpaceMiddle =
        realMajoranaSpaceMiddle *
          (realMajoranaTimeHead * realMajoranaSpaceTail) := by
    calc
      _ = realMajoranaTimeHead *
            (realMajoranaSpaceTail * realMajoranaSpaceMiddle) := by rw [mul_assoc]
      _ = realMajoranaTimeHead *
            (-(realMajoranaSpaceMiddle * realMajoranaSpaceTail)) := by rw [hymz]
      _ = -((realMajoranaTimeHead * realMajoranaSpaceMiddle) *
            realMajoranaSpaceTail) := by noncomm_ring
      _ = -((-(realMajoranaSpaceMiddle * realMajoranaTimeHead)) *
            realMajoranaSpaceTail) := by rw [htym']
      _ = (realMajoranaSpaceMiddle * realMajoranaTimeHead) *
            realMajoranaSpaceTail := by simp only [neg_mul, neg_neg]
      _ = realMajoranaSpaceMiddle *
            (realMajoranaTimeHead * realMajoranaSpaceTail) := by rw [← mul_assoc]
  exact ⟨hT, hZ, by rw [hBX]; simp, by rw [hBY]; simp⟩

private theorem rindlerMajoranaBivector_square :
    rindlerMajoranaBivector * rindlerMajoranaBivector = 1 := by
  have ht2 := realMajorana_minkowski_diagonal_squares.1
  have hz2 := realMajorana_minkowski_diagonal_squares.2.2.2
  have htz := realMajoranaHead_tail_cross_anticommutators.2.1
  have hzt : realMajoranaSpaceTail * realMajoranaTimeHead =
      -(realMajoranaTimeHead * realMajoranaSpaceTail) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using htz)
  calc
    rindlerMajoranaBivector * rindlerMajoranaBivector =
        realMajoranaTimeHead *
          (realMajoranaSpaceTail * realMajoranaTimeHead) *
          realMajoranaSpaceTail := by
            simp only [rindlerMajoranaBivector]
            noncomm_ring
    _ = realMajoranaTimeHead *
          (-(realMajoranaTimeHead * realMajoranaSpaceTail)) *
          realMajoranaSpaceTail := by rw [hzt]
    _ = 1 := by
          simp [mul_assoc, ht2, hz2]

/-- The explicit rotor and its reverse multiply to one in the real CAR
algebra. -/
theorem rindlerMajoranaSpinRotor_mul_reverse (s : ℝ) :
    rindlerMajoranaSpinRotor s * rindlerMajoranaSpinRotorReverse s = 1 := by
  have hB2 := rindlerMajoranaBivector_square
  calc
    _ = (Real.cosh (s / 2) ^ 2 - Real.sinh (s / 2) ^ 2) •
          (1 : realThreeMatrixGradedTensor) := by
      simp only [rindlerMajoranaSpinRotor, rindlerMajoranaSpinRotorReverse]
      noncomm_ring
      rw [hB2]
      module
    _ = 1 := by
      rw [Real.cosh_sq_sub_sinh_sq]
      simp

/-- The CAR rotors form the expected one-parameter hyperbolic subgroup;
their parameter addition agrees with the existing Rindler boost law. -/
theorem rindlerMajoranaSpinRotor_mul (s t : ℝ) :
    rindlerMajoranaSpinRotor s * rindlerMajoranaSpinRotor t =
      rindlerMajoranaSpinRotor (s + t) := by
  have hB2 := rindlerMajoranaBivector_square
  have hArg : (s + t) / 2 = s / 2 + t / 2 := by ring
  have hR (u : ℝ) : rindlerMajoranaSpinRotor u =
      InfoGeometry.OperatorAlgebra.hyperbolicRotor rindlerMajoranaBivector
        (Real.cosh (u / 2)) (-Real.sinh (u / 2)) := by
    simp only [rindlerMajoranaSpinRotor,
      InfoGeometry.OperatorAlgebra.hyperbolicRotor]
    rw [sub_eq_add_neg, ← neg_smul]
  have hc : Real.cosh (s / 2) * Real.cosh (t / 2) +
      (-Real.sinh (s / 2)) * (-Real.sinh (t / 2)) =
        Real.cosh ((s + t) / 2) := by
    rw [hArg, Real.cosh_add]
    ring
  have hs : Real.cosh (s / 2) * (-Real.sinh (t / 2)) +
      (-Real.sinh (s / 2)) * Real.cosh (t / 2) =
        -Real.sinh ((s + t) / 2) := by
    rw [hArg, Real.sinh_add]
    ring
  rw [hR s, hR t, hR (s + t),
    InfoGeometry.OperatorAlgebra.hyperbolicRotor_mul
      rindlerMajoranaBivector hB2, hc, hs]

/-- The reverse CAR rotors obey the same additive law.  The order of the
factors is retained: this is the reverse-product law needed to compose the
actual sandwich action on the real CAR algebra. -/
theorem rindlerMajoranaSpinRotorReverse_mul (s t : ℝ) :
    rindlerMajoranaSpinRotorReverse s * rindlerMajoranaSpinRotorReverse t =
      rindlerMajoranaSpinRotorReverse (s + t) := by
  have hB2 := rindlerMajoranaBivector_square
  have hArg : (s + t) / 2 = s / 2 + t / 2 := by ring
  simp only [rindlerMajoranaSpinRotorReverse]
  have hc : Real.cosh (s / 2) * Real.cosh (t / 2) +
      Real.sinh (s / 2) * Real.sinh (t / 2) = Real.cosh ((s + t) / 2) := by
    rw [hArg, Real.cosh_add]
  have hs : Real.cosh (s / 2) * Real.sinh (t / 2) +
      Real.sinh (s / 2) * Real.cosh (t / 2) = Real.sinh ((s + t) / 2) := by
    rw [hArg, Real.sinh_add]
    ring
  calc
    _ = (Real.cosh (s / 2) * Real.cosh (t / 2) +
          Real.sinh (s / 2) * Real.sinh (t / 2)) •
          (1 : realThreeMatrixGradedTensor) +
        (Real.cosh (s / 2) * Real.sinh (t / 2) +
          Real.sinh (s / 2) * Real.cosh (t / 2)) • rindlerMajoranaBivector := by
      noncomm_ring
      rw [hB2]
      module
    _ = _ := by rw [hc, hs]

/-- The conjugation action of the real CAR boost rotor is a genuine
one-parameter action: two successive rapidities compose to their sum on every
element of the noncommutative CAR algebra. -/
theorem rindlerMajoranaSpinRotor_sandwich_comp (s t : ℝ)
    (A : realThreeMatrixGradedTensor) :
    rindlerMajoranaSpinRotor s *
        (rindlerMajoranaSpinRotor t * A * rindlerMajoranaSpinRotorReverse t) *
        rindlerMajoranaSpinRotorReverse s =
      rindlerMajoranaSpinRotor (s + t) * A *
        rindlerMajoranaSpinRotorReverse (s + t) := by
  calc
    _ = (rindlerMajoranaSpinRotor s * rindlerMajoranaSpinRotor t) * A *
        (rindlerMajoranaSpinRotorReverse t * rindlerMajoranaSpinRotorReverse s) := by
          noncomm_ring
    _ = _ := by
      rw [rindlerMajoranaSpinRotor_mul, rindlerMajoranaSpinRotorReverse_mul]
      rw [add_comm t s]

private theorem rindlerMajoranaBivector_double_conjugates :
    rindlerMajoranaBivector * realMajoranaTimeHead * rindlerMajoranaBivector =
        -realMajoranaTimeHead ∧
    rindlerMajoranaBivector * realMajoranaSpaceTail * rindlerMajoranaBivector =
        -realMajoranaSpaceTail ∧
    rindlerMajoranaBivector * realMajoranaSpaceHead * rindlerMajoranaBivector =
        realMajoranaSpaceHead ∧
    rindlerMajoranaBivector * realMajoranaSpaceMiddle * rindlerMajoranaBivector =
        realMajoranaSpaceMiddle := by
  obtain ⟨hT, hZ, hX, hY⟩ := rindlerBivector_commutators
  let B := realMajoranaTimeHead * realMajoranaSpaceTail
  have hB2 : B * B = 1 := by
    simpa [B, rindlerMajoranaBivector] using rindlerMajoranaBivector_square
  have hT' : B * realMajoranaTimeHead - realMajoranaTimeHead * B =
      -(2 : ℝ) • realMajoranaSpaceTail := by simpa [B] using hT
  have hZ' : B * realMajoranaSpaceTail - realMajoranaSpaceTail * B =
      -(2 : ℝ) • realMajoranaTimeHead := by simpa [B] using hZ
  have hX' : B * realMajoranaSpaceHead - realMajoranaSpaceHead * B = 0 := by
    simpa [B] using hX
  have hY' : B * realMajoranaSpaceMiddle - realMajoranaSpaceMiddle * B = 0 := by
    simpa [B] using hY
  have hzt' : realMajoranaSpaceTail * realMajoranaTimeHead =
      -(realMajoranaTimeHead * realMajoranaSpaceTail) :=
    eq_neg_of_add_eq_zero_left
      (by simpa [add_comm] using realMajoranaHead_tail_cross_anticommutators.2.1)
  have hTailB : realMajoranaSpaceTail * B = realMajoranaTimeHead := by
    dsimp [B]
    calc
      realMajoranaSpaceTail * (realMajoranaTimeHead * realMajoranaSpaceTail) =
          (realMajoranaSpaceTail * realMajoranaTimeHead) * realMajoranaSpaceTail := by
            noncomm_ring
      _ = -(realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaSpaceTail := by
            rw [hzt']
      _ = -((realMajoranaTimeHead * realMajoranaSpaceTail) *
          realMajoranaSpaceTail) := by simp
      _ = -(realMajoranaTimeHead *
          (realMajoranaSpaceTail * realMajoranaSpaceTail)) := by
            congr 1
            noncomm_ring
      _ = realMajoranaTimeHead := by
            rw [realMajorana_minkowski_diagonal_squares.2.2.2]
            simp
  have hHeadB : realMajoranaTimeHead * B = realMajoranaSpaceTail := by
    dsimp [B]
    rw [← mul_assoc, realMajorana_minkowski_diagonal_squares.1, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      B * realMajoranaTimeHead * B =
          (B * realMajoranaTimeHead - realMajoranaTimeHead * B) * B +
            realMajoranaTimeHead * (B * B) := by noncomm_ring
      _ = -realMajoranaTimeHead := by
            rw [hT', hB2, smul_mul_assoc, hTailB]
            simp only [mul_one]
            module
  · calc
      B * realMajoranaSpaceTail * B =
          (B * realMajoranaSpaceTail - realMajoranaSpaceTail * B) * B +
            realMajoranaSpaceTail * (B * B) := by noncomm_ring
      _ = -realMajoranaSpaceTail := by
            rw [hZ', hB2, smul_mul_assoc, hHeadB]
            simp only [mul_one]
            module
  · have hComm : B * realMajoranaSpaceHead = realMajoranaSpaceHead * B :=
      sub_eq_zero.mp hX'
    calc
      B * realMajoranaSpaceHead * B =
          (B * realMajoranaSpaceHead - realMajoranaSpaceHead * B) * B +
            realMajoranaSpaceHead * (B * B) := by noncomm_ring
      _ = realMajoranaSpaceHead * (B * B) := by rw [hComm]; simp
      _ = realMajoranaSpaceHead := by rw [hB2, mul_one]
  · have hComm : B * realMajoranaSpaceMiddle = realMajoranaSpaceMiddle * B :=
      sub_eq_zero.mp hY'
    calc
      B * realMajoranaSpaceMiddle * B =
          (B * realMajoranaSpaceMiddle - realMajoranaSpaceMiddle * B) * B +
            realMajoranaSpaceMiddle * (B * B) := by noncomm_ring
      _ = realMajoranaSpaceMiddle * (B * B) := by rw [hComm]; simp
      _ = realMajoranaSpaceMiddle := by rw [hB2, mul_one]

private theorem rindlerMajoranaRotor_time_action (s : ℝ) :
    rindlerMajoranaSpinRotor s * realMajoranaTimeHead *
        rindlerMajoranaSpinRotorReverse s =
      Real.cosh s • realMajoranaTimeHead + Real.sinh s • realMajoranaSpaceTail := by
  have htz := realMajoranaHead_tail_cross_anticommutators.2.1
  have hzt : realMajoranaSpaceTail * realMajoranaTimeHead =
      -(realMajoranaTimeHead * realMajoranaSpaceTail) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using htz)
  have htb : realMajoranaTimeHead * rindlerMajoranaBivector =
      realMajoranaSpaceTail := by
    simp only [rindlerMajoranaBivector]
    calc
      realMajoranaTimeHead *
          (realMajoranaTimeHead * realMajoranaSpaceTail) =
          (realMajoranaTimeHead * realMajoranaTimeHead) *
            realMajoranaSpaceTail := (mul_assoc _ _ _).symm
      _ = realMajoranaSpaceTail := by
        rw [realMajorana_minkowski_diagonal_squares.1, one_mul]
  have hbt : rindlerMajoranaBivector * realMajoranaTimeHead =
      -realMajoranaSpaceTail := by
    simp only [rindlerMajoranaBivector]
    calc
      (realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaTimeHead =
          realMajoranaTimeHead * (realMajoranaSpaceTail * realMajoranaTimeHead) := by
            rw [mul_assoc]
      _ = realMajoranaTimeHead *
          (-(realMajoranaTimeHead * realMajoranaSpaceTail)) := by rw [hzt]
      _ = -realMajoranaSpaceTail := by
        rw [mul_neg, ← mul_assoc, realMajorana_minkowski_diagonal_squares.1]
        simp
  have hdouble := rindlerMajoranaBivector_double_conjugates.1
  have hc : Real.cosh s = Real.cosh (s / 2) ^ 2 +
      Real.sinh (s / 2) ^ 2 := by
    rw [show s = 2 * (s / 2) by ring, Real.cosh_two_mul]
    congr 1 <;> ring_nf
  have hs : Real.sinh s = 2 * Real.sinh (s / 2) * Real.cosh (s / 2) := by
    rw [show s = 2 * (s / 2) by ring, Real.sinh_two_mul]
    congr 1 <;> ring_nf
  have hs' : Real.sinh s = 2 * Real.cosh (s / 2) * Real.sinh (s / 2) := by
    rw [hs]
    ring
  calc
    _ = (Real.cosh (s / 2) ^ 2 + Real.sinh (s / 2) ^ 2) •
          realMajoranaTimeHead +
        (2 * Real.cosh (s / 2) * Real.sinh (s / 2)) •
          realMajoranaSpaceTail := by
      simp only [rindlerMajoranaSpinRotor,
        rindlerMajoranaSpinRotorReverse]
      noncomm_ring
      simp only [← mul_assoc]
      rw [hdouble, htb, hbt]
      module
    _ = Real.cosh s • realMajoranaTimeHead +
        Real.sinh s • realMajoranaSpaceTail := by rw [hc, hs']

private theorem rindlerMajoranaRotor_tail_action (s : ℝ) :
    rindlerMajoranaSpinRotor s * realMajoranaSpaceTail *
        rindlerMajoranaSpinRotorReverse s =
      Real.sinh s • realMajoranaTimeHead + Real.cosh s • realMajoranaSpaceTail := by
  have htz := realMajoranaHead_tail_cross_anticommutators.2.1
  have hzt : realMajoranaSpaceTail * realMajoranaTimeHead =
      -(realMajoranaTimeHead * realMajoranaSpaceTail) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using htz)
  have hz2 := realMajorana_minkowski_diagonal_squares.2.2.2
  have hBz : rindlerMajoranaBivector * realMajoranaSpaceTail =
      -realMajoranaTimeHead := by
    simp only [rindlerMajoranaBivector]
    calc
      (realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaSpaceTail =
          realMajoranaTimeHead *
            (realMajoranaSpaceTail * realMajoranaSpaceTail) := by rw [mul_assoc]
      _ = -realMajoranaTimeHead := by rw [hz2]; simp
  have hzb : realMajoranaSpaceTail * rindlerMajoranaBivector =
      realMajoranaTimeHead := by
    simp only [rindlerMajoranaBivector]
    calc
      realMajoranaSpaceTail *
          (realMajoranaTimeHead * realMajoranaSpaceTail) =
          (realMajoranaSpaceTail * realMajoranaTimeHead) *
            realMajoranaSpaceTail := by rw [mul_assoc]
      _ = -(realMajoranaTimeHead * realMajoranaSpaceTail) *
          realMajoranaSpaceTail := by rw [hzt]
      _ = -realMajoranaTimeHead *
          (realMajoranaSpaceTail * realMajoranaSpaceTail) := by
        calc
          -(realMajoranaTimeHead * realMajoranaSpaceTail) * realMajoranaSpaceTail =
              -((realMajoranaTimeHead * realMajoranaSpaceTail) *
                realMajoranaSpaceTail) := by rw [neg_mul]
          _ = -(realMajoranaTimeHead *
              (realMajoranaSpaceTail * realMajoranaSpaceTail)) :=
                congrArg Neg.neg (mul_assoc _ _ _)
          _ = -realMajoranaTimeHead *
              (realMajoranaSpaceTail * realMajoranaSpaceTail) := by rw [neg_mul]
      _ = realMajoranaTimeHead := by rw [hz2]; simp
  have hdouble := rindlerMajoranaBivector_double_conjugates.2.1
  have hc : Real.cosh s = Real.cosh (s / 2) ^ 2 +
      Real.sinh (s / 2) ^ 2 := by
    rw [show s = 2 * (s / 2) by ring, Real.cosh_two_mul]
    congr 1 <;> ring_nf
  have hs : Real.sinh s = 2 * Real.sinh (s / 2) * Real.cosh (s / 2) := by
    rw [show s = 2 * (s / 2) by ring, Real.sinh_two_mul]
    congr 1 <;> ring_nf
  have hs' : Real.sinh s = 2 * Real.cosh (s / 2) * Real.sinh (s / 2) := by
    rw [hs]
    ring
  calc
    _ = (Real.cosh (s / 2) ^ 2 + Real.sinh (s / 2) ^ 2) •
          realMajoranaSpaceTail +
        (2 * Real.cosh (s / 2) * Real.sinh (s / 2)) •
          realMajoranaTimeHead := by
      simp only [rindlerMajoranaSpinRotor,
        rindlerMajoranaSpinRotorReverse]
      noncomm_ring
      simp only [← mul_assoc]
      rw [hdouble, hBz, hzb]
      module
    _ = Real.sinh s • realMajoranaTimeHead +
        Real.cosh s • realMajoranaSpaceTail := by
      rw [hc, hs']
      module

/-! ### Null CAR channels and the real boost flow

The two real Majorana directions in the longitudinal Rindler plane have
opposite squares. Their normalized sums are therefore null generators. This
is the real Clifford/CAR version of the two light-cone channels; the boost
acts on them with reciprocal positive factors. -/

/-- Positive null channel in the real longitudinal CAR plane. -/
def rindlerNullMajoranaPlus : realThreeMatrixGradedTensor :=
  (1 / 2 : ℝ) • (realMajoranaTimeHead + realMajoranaSpaceTail)

/-- Negative null channel in the real longitudinal CAR plane. -/
def rindlerNullMajoranaMinus : realThreeMatrixGradedTensor :=
  (1 / 2 : ℝ) • (realMajoranaTimeHead - realMajoranaSpaceTail)

/-- The real Rindler null channels are nilpotent CAR generators and the
finite Majorana rotor transports them by reciprocal boost weights. The
carrier is the existing three-factor Koszul-graded real matrix algebra. -/
theorem rindlerNullMajorana_car_and_boost (s : ℝ) :
    rindlerNullMajoranaPlus * rindlerNullMajoranaPlus = 0 ∧
    rindlerNullMajoranaMinus * rindlerNullMajoranaMinus = 0 ∧
    rindlerNullMajoranaPlus * rindlerNullMajoranaMinus +
      rindlerNullMajoranaMinus * rindlerNullMajoranaPlus = 1 ∧
    rindlerMajoranaSpinRotor s * rindlerNullMajoranaPlus *
        rindlerMajoranaSpinRotorReverse s =
      (Real.cosh s + Real.sinh s) • rindlerNullMajoranaPlus ∧
    rindlerMajoranaSpinRotor s * rindlerNullMajoranaMinus *
        rindlerMajoranaSpinRotorReverse s =
      (Real.cosh s - Real.sinh s) • rindlerNullMajoranaMinus := by
  have hT := realMajorana_minkowski_diagonal_squares.1
  have hZ := realMajorana_minkowski_diagonal_squares.2.2.2
  have hTZ := realMajoranaHead_tail_cross_anticommutators.2.1
  have hPlusBoost :
      rindlerMajoranaSpinRotor s *
          (realMajoranaTimeHead + realMajoranaSpaceTail) *
          rindlerMajoranaSpinRotorReverse s =
        (Real.cosh s + Real.sinh s) •
          (realMajoranaTimeHead + realMajoranaSpaceTail) := by
    calc
      _ = rindlerMajoranaSpinRotor s * realMajoranaTimeHead *
            rindlerMajoranaSpinRotorReverse s +
          rindlerMajoranaSpinRotor s * realMajoranaSpaceTail *
            rindlerMajoranaSpinRotorReverse s := by noncomm_ring
      _ = _ := by rw [rindlerMajoranaRotor_time_action,
        rindlerMajoranaRotor_tail_action]; module
  have hMinusBoost :
      rindlerMajoranaSpinRotor s *
          (realMajoranaTimeHead - realMajoranaSpaceTail) *
          rindlerMajoranaSpinRotorReverse s =
        (Real.cosh s - Real.sinh s) •
          (realMajoranaTimeHead - realMajoranaSpaceTail) := by
    calc
      _ = rindlerMajoranaSpinRotor s * realMajoranaTimeHead *
            rindlerMajoranaSpinRotorReverse s -
          rindlerMajoranaSpinRotor s * realMajoranaSpaceTail *
            rindlerMajoranaSpinRotorReverse s := by noncomm_ring
      _ = _ := by rw [rindlerMajoranaRotor_time_action,
        rindlerMajoranaRotor_tail_action]; module
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rindlerNullMajoranaPlus]
    rw [smul_mul_smul]
    rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    have hZT : realMajoranaSpaceTail * realMajoranaTimeHead =
        -(realMajoranaTimeHead * realMajoranaSpaceTail) :=
      eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hTZ)
    have h : (realMajoranaTimeHead + realMajoranaSpaceTail) ^ 2 = 0 := by
      rw [pow_two]
      calc
        (realMajoranaTimeHead + realMajoranaSpaceTail) *
            (realMajoranaTimeHead + realMajoranaSpaceTail) =
          realMajoranaTimeHead * realMajoranaTimeHead +
            realMajoranaTimeHead * realMajoranaSpaceTail +
            realMajoranaSpaceTail * realMajoranaTimeHead +
            realMajoranaSpaceTail * realMajoranaSpaceTail := by noncomm_ring
        _ = 0 := by rw [hT, hZ, hZT]; module
    simpa [pow_two] using congrArg (fun x : realThreeMatrixGradedTensor => (1 / 4 : ℝ) • x) h
  · rw [rindlerNullMajoranaMinus]
    rw [smul_mul_smul]
    rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    have hZT : realMajoranaSpaceTail * realMajoranaTimeHead =
        -(realMajoranaTimeHead * realMajoranaSpaceTail) :=
      eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hTZ)
    have h : (realMajoranaTimeHead - realMajoranaSpaceTail) ^ 2 = 0 := by
      rw [pow_two]
      calc
        (realMajoranaTimeHead - realMajoranaSpaceTail) *
            (realMajoranaTimeHead - realMajoranaSpaceTail) =
          realMajoranaTimeHead * realMajoranaTimeHead -
            realMajoranaTimeHead * realMajoranaSpaceTail -
            realMajoranaSpaceTail * realMajoranaTimeHead +
            realMajoranaSpaceTail * realMajoranaSpaceTail := by noncomm_ring
        _ = 0 := by rw [hT, hZ, hZT]; module
    simpa [pow_two] using congrArg (fun x : realThreeMatrixGradedTensor => (1 / 4 : ℝ) • x) h
  · rw [rindlerNullMajoranaPlus, rindlerNullMajoranaMinus]
    rw [smul_mul_smul, smul_mul_smul]
    rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    have h : (realMajoranaTimeHead + realMajoranaSpaceTail) *
          (realMajoranaTimeHead - realMajoranaSpaceTail) +
        (realMajoranaTimeHead - realMajoranaSpaceTail) *
          (realMajoranaTimeHead + realMajoranaSpaceTail) = 4 • (1 : realThreeMatrixGradedTensor) := by
      calc
        _ = 2 • (realMajoranaTimeHead * realMajoranaTimeHead -
            realMajoranaSpaceTail * realMajoranaSpaceTail) := by noncomm_ring
        _ = 4 • (1 : realThreeMatrixGradedTensor) := by rw [hT, hZ]; module
    calc
      (1 / 4 : ℝ) • ((realMajoranaTimeHead + realMajoranaSpaceTail) *
          (realMajoranaTimeHead - realMajoranaSpaceTail)) +
        (1 / 4 : ℝ) • ((realMajoranaTimeHead - realMajoranaSpaceTail) *
          (realMajoranaTimeHead + realMajoranaSpaceTail))
          = (1 / 4 : ℝ) • ((realMajoranaTimeHead + realMajoranaSpaceTail) *
              (realMajoranaTimeHead - realMajoranaSpaceTail) +
            (realMajoranaTimeHead - realMajoranaSpaceTail) *
              (realMajoranaTimeHead + realMajoranaSpaceTail)) := by rw [← smul_add]
      _ = 1 := by rw [h]; module
  · rw [rindlerNullMajoranaPlus]
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [hPlusBoost]
    simp only [smul_smul]
    module
  · rw [rindlerNullMajoranaMinus]
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [hMinusBoost]
    simp only [smul_smul]
    module

/-- The null-channel CAR relations and reciprocal Rindler boost law hold
after transport to the shared real doubled-Krein operator space. This is the
same carrier used by the Peirce translation and circular-curvature bridges. -/
theorem rindlerNullMajorana_onKrein_car_and_boost (s : ℝ) :
    realThreeMatrixTensorOnH4 rindlerNullMajoranaPlus *
        realThreeMatrixTensorOnH4 rindlerNullMajoranaPlus = 0 ∧
    realThreeMatrixTensorOnH4 rindlerNullMajoranaMinus *
        realThreeMatrixTensorOnH4 rindlerNullMajoranaMinus = 0 ∧
    realThreeMatrixTensorOnH4 rindlerNullMajoranaPlus *
        realThreeMatrixTensorOnH4 rindlerNullMajoranaMinus +
      realThreeMatrixTensorOnH4 rindlerNullMajoranaMinus *
        realThreeMatrixTensorOnH4 rindlerNullMajoranaPlus = 1 ∧
    realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
        realThreeMatrixTensorOnH4 rindlerNullMajoranaPlus *
        realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) =
      (Real.cosh s + Real.sinh s) •
        realThreeMatrixTensorOnH4 rindlerNullMajoranaPlus ∧
    realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
        realThreeMatrixTensorOnH4 rindlerNullMajoranaMinus *
        realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) =
      (Real.cosh s - Real.sinh s) •
        realThreeMatrixTensorOnH4 rindlerNullMajoranaMinus := by
  have h := rindlerNullMajorana_car_and_boost s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul, map_zero] using
      congrArg realThreeMatrixTensorOnH4 h.1
  · simpa only [map_mul, map_zero] using
      congrArg realThreeMatrixTensorOnH4 h.2.1
  · simpa only [map_mul, map_add, map_one] using
      congrArg realThreeMatrixTensorOnH4 h.2.2.1
  · simpa only [map_mul, map_smul] using
      congrArg realThreeMatrixTensorOnH4 h.2.2.2.1
  · simpa only [map_mul, map_smul] using
      congrArg realThreeMatrixTensorOnH4 h.2.2.2.2

private theorem rindlerMajoranaRotor_fixed_action
    (s : ℝ) (γ : realThreeMatrixGradedTensor)
    (hcomm : rindlerMajoranaBivector * γ = γ * rindlerMajoranaBivector) :
    rindlerMajoranaSpinRotor s * γ * rindlerMajoranaSpinRotorReverse s = γ := by
  have hRcomm : rindlerMajoranaSpinRotor s * γ =
      γ * rindlerMajoranaSpinRotor s := by
    simp only [rindlerMajoranaSpinRotor]
    noncomm_ring
    rw [hcomm]
  calc
    rindlerMajoranaSpinRotor s * γ * rindlerMajoranaSpinRotorReverse s =
        γ * (rindlerMajoranaSpinRotor s *
          rindlerMajoranaSpinRotorReverse s) := by
      rw [hRcomm]
      noncomm_ring
    _ = γ := by rw [rindlerMajoranaSpinRotor_mul_reverse]; simp

private theorem rindlerMajoranaRotor_spaceHead_action (s : ℝ) :
    rindlerMajoranaSpinRotor s * realMajoranaSpaceHead *
        rindlerMajoranaSpinRotorReverse s = realMajoranaSpaceHead := by
  obtain ⟨_, _, hX, _⟩ := rindlerBivector_commutators
  exact rindlerMajoranaRotor_fixed_action s realMajoranaSpaceHead
    (sub_eq_zero.mp hX)

private theorem rindlerMajoranaRotor_spaceMiddle_action (s : ℝ) :
    rindlerMajoranaSpinRotor s * realMajoranaSpaceMiddle *
        rindlerMajoranaSpinRotorReverse s = realMajoranaSpaceMiddle := by
  obtain ⟨_, _, _, hY⟩ := rindlerBivector_commutators
  exact rindlerMajoranaRotor_fixed_action s realMajoranaSpaceMiddle
    (sub_eq_zero.mp hY)

/-- The finite real CAR rotor conjugates the complete Majorana contraction
by the same Rindler boost as the existing spacetime/Lipschitz owner. This
proves the finite action on the actual graded CAR algebra, extending the
infinitesimal commutator identity above. -/
theorem rindlerMajoranaSpinRotor_sandwich
    (s : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    rindlerMajoranaSpinRotor s * realMinkowskiMajorana X *
        rindlerMajoranaSpinRotorReverse s =
      realMinkowskiMajorana
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) := by
  rw [realMinkowskiMajorana]
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add]
  rw [rindlerMajoranaRotor_time_action,
    rindlerMajoranaRotor_spaceHead_action,
    rindlerMajoranaRotor_spaceMiddle_action,
    rindlerMajoranaRotor_tail_action]
  cases X with
  | mk t x y z =>
      simp [realMinkowskiMajorana,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost]
      module

/-- The existing real CAR boost rotor acts on the actual doubled-Krein
endomorphism carrier by the same Rindler boost.  This is the finite spin
action transported through the owner's algebra equivalence, so the result
is an equality in `Module.End ℝ KreinFrame4`, not only in the abstract graded
tensor algebra. -/
theorem rindlerMajoranaSpinRotor_onKrein_sandwich
    (s : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
        realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) =
      realThreeMatrixTensorOnH4
        (realMinkowskiMajorana
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s)) := by
  calc
    _ = realThreeMatrixTensorOnH4
        (rindlerMajoranaSpinRotor s * realMinkowskiMajorana X *
          rindlerMajoranaSpinRotorReverse s) := by rw [map_mul, map_mul]
    _ = _ := congrArg realThreeMatrixTensorOnH4
      (rindlerMajoranaSpinRotor_sandwich s X)

/-- The negative-sheet modular flow on the real doubled scalar carrier and
the finite CAR spin-rotor action have the same physical four-vector
readout.  The two transverse coordinates are retained unchanged.  This is a
flat Rindler result: it identifies existing modular and CAR actions without
asserting a curved spinor-bundle Kosmann derivative. -/
theorem negativeSheetModularFlow_eq_realCARSpinRotor_action
    (s : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
        realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) =
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana
        ⟨WithLp.fst (InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
            (E := ℝ) (-(InfoGeometry.Krein.spectral_epsilon (E := ℝ))) s
            (InfoGeometry.Krein.to_doubled X.t X.z)),
          X.x, X.y,
          WithLp.snd (InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
            (E := ℝ) (-(InfoGeometry.Krein.spectral_epsilon (E := ℝ))) s
            (InfoGeometry.Krein.to_doubled X.t X.z))⟩) := by
  rw [rindlerMajoranaSpinRotor_onKrein_sandwich]
  rw [realThreeMatrixTensorOnH4.injective.eq_iff]
  cases X with
  | mk t x y z =>
      have hFlow := InfoGeometry.Canonical.SouriauKillingLipschitzBridge.negativeSheet_modularFlow_eq_boostFlow s (t, z)
      have hTime := congrArg WithLp.fst hFlow
      have hSpace := congrArg WithLp.snd hFlow
      simp only [InfoGeometry.Krein.fst_to_doubled] at hTime
      simp only [InfoGeometry.Krein.snd_to_doubled] at hSpace
      simp only [InfoGeometry.Canonical.SouriauKillingLipschitzBridge.boostFlow] at hTime hSpace
      have hVec :
          InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost
              ⟨t, x, y, z⟩ s =
            ⟨WithLp.fst (InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
                (E := ℝ) (-(InfoGeometry.Krein.spectral_epsilon (E := ℝ))) s
                (InfoGeometry.Krein.to_doubled t z)),
              x, y,
              WithLp.snd (InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
                (E := ℝ) (-(InfoGeometry.Krein.spectral_epsilon (E := ℝ))) s
                (InfoGeometry.Krein.to_doubled t z))⟩ := by
        ext
        · change t * Real.cosh s + z * Real.sinh s = _
          calc
            t * Real.cosh s + z * Real.sinh s =
                Real.cosh s * t + Real.sinh s * z := by ring
            _ = _ := hTime.symm
        · rfl
        · rfl
        · change z * Real.cosh s + t * Real.sinh s = _
          calc
            z * Real.cosh s + t * Real.sinh s =
                Real.sinh s * t + Real.cosh s * z := by ring
            _ = _ := hSpace.symm
      exact congrArg realMinkowskiMajorana hVec

/-- Composing the real CAR boost action on two successive rapidity intervals
agrees with the Rindler boost at the summed rapidity.  This is the group
action law on the actual real doubled-Krein endomorphism carrier. -/
theorem rindlerMajoranaSpinRotor_comp_eq_rindlerBoost
    (s t : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
        (realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor t) *
          realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
          realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse t)) *
        realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) =
      realThreeMatrixTensorOnH4
        (realMinkowskiMajorana
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X (s + t))) := by
  calc
    _ = realThreeMatrixTensorOnH4
        (rindlerMajoranaSpinRotor s *
          (rindlerMajoranaSpinRotor t * realMinkowskiMajorana X *
            rindlerMajoranaSpinRotorReverse t) *
          rindlerMajoranaSpinRotorReverse s) := by
            simp only [map_mul]
    _ = realThreeMatrixTensorOnH4
        (rindlerMajoranaSpinRotor (s + t) * realMinkowskiMajorana X *
          rindlerMajoranaSpinRotorReverse (s + t)) :=
            congrArg realThreeMatrixTensorOnH4
              (rindlerMajoranaSpinRotor_sandwich_comp s t
                (realMinkowskiMajorana X))
    _ = _ := by
      simp only [map_mul]
      exact rindlerMajoranaSpinRotor_onKrein_sandwich (s + t) X

/-! ## Transport of the real CAR boost into the Clifford inductive limit -/

/-- The actual three-mode real graded CAR algebra is the stage-three matrix
algebra of the existing `Cl(1,1)` tower. The coordinate change composes the
real CAR Morita equivalence with the explicitly ordered occupation basis and
the circular Peirce index permutation already owned by the finite JW and
soldering modules. -/
noncomputable def realCARStageThreeEquiv :
    realThreeMatrixGradedTensor ≃ₐ[ℝ]
      InfoGeometry.Clifford.Cl11TensorTower.MatStage 3 :=
  (realThreeMatrixTensorToFin8).trans
    ((Matrix.reindexAlgEquiv ℝ ℝ realThreePeirceIndex).symm.trans
      InfoGeometry.Clifford.Cl33FiniteJWMajoranaMatrix.stage3ToMatrix8.symm)

/-- The canonical algebra map from the existing real CAR carrier to the
algebraic `Cl(1,1)` inductive limit, through its genuine stage-three
identification. -/
noncomputable def realCARToCliffordLimit :
    realThreeMatrixGradedTensor →ₐ[ℝ]
      InfoGeometry.Canonical.Cl11TensorInductiveLimit.Limit :=
  (InfoGeometry.Canonical.Cl11TensorInductiveLimit.ofStageAlgHom 3).comp
    realCARStageThreeEquiv.toAlgHom

/-- The finite CAR-to-limit map is injective: neither the stage-three
coordinate equivalence nor the Clifford tower's canonical stage map collapses
CAR elements. -/
theorem realCARToCliffordLimit_injective :
    Function.Injective realCARToCliffordLimit := by
  apply (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_injective
    InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond
    (fun n => InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_injective n) 3).comp
  exact realCARStageThreeEquiv.injective

/-- The rapidity-addition law for the real Rindler CAR sandwich survives in
the actual algebraic Clifford inductive limit.  This is a colimit transport of
the finite noncommutative action, not merely a scalar-parameter tower law. -/
theorem rindlerMajoranaSpinRotor_sandwich_comp_inCliffordLimit
    (s t : ℝ) (A : realThreeMatrixGradedTensor) :
    realCARToCliffordLimit (rindlerMajoranaSpinRotor s) *
        (realCARToCliffordLimit (rindlerMajoranaSpinRotor t) *
          realCARToCliffordLimit A *
          realCARToCliffordLimit (rindlerMajoranaSpinRotorReverse t)) *
        realCARToCliffordLimit (rindlerMajoranaSpinRotorReverse s) =
      realCARToCliffordLimit (rindlerMajoranaSpinRotor (s + t) * A *
        rindlerMajoranaSpinRotorReverse (s + t)) := by
  have h := congrArg realCARToCliffordLimit
    (rindlerMajoranaSpinRotor_sandwich_comp s t A)
  simpa only [map_mul] using h

/-- On a Minkowski Majorana generator, the limit-valued CAR flow at summed
rapidity has the existing Rindler-boost readout, now inside the algebraic
Clifford colimit carrier. -/
theorem rindlerMajoranaSpinRotor_comp_boost_inCliffordLimit
    (s t : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realCARToCliffordLimit (rindlerMajoranaSpinRotor s) *
        (realCARToCliffordLimit (rindlerMajoranaSpinRotor t) *
          realCARToCliffordLimit (realMinkowskiMajorana X) *
          realCARToCliffordLimit (rindlerMajoranaSpinRotorReverse t)) *
        realCARToCliffordLimit (rindlerMajoranaSpinRotorReverse s) =
      realCARToCliffordLimit (realMinkowskiMajorana
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X (s + t))) := by
  have hCAR :
      rindlerMajoranaSpinRotor s *
          (rindlerMajoranaSpinRotor t * realMinkowskiMajorana X *
            rindlerMajoranaSpinRotorReverse t) *
          rindlerMajoranaSpinRotorReverse s =
        realMinkowskiMajorana
          (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X (s + t)) := by
    apply realThreeMatrixTensorOnH4.injective
    simpa only [map_mul] using rindlerMajoranaSpinRotor_comp_eq_rindlerBoost s t X
  have h := congrArg realCARToCliffordLimit hCAR
  simpa only [map_mul] using h

/-- The infinitesimal Rindler Killing action on the genuine real Majorana
contraction is the adjoint action of its CAR bivector generator. In
particular, it identifies the operator action with the existing Souriau
`rindlerKillingGenerator`, rather than only recording invariance of the
quadratic square. -/
theorem rindlerMajoranaSpinGenerator_commutator
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    rindlerMajoranaSpinGenerator * realMinkowskiMajorana X -
        realMinkowskiMajorana X * rindlerMajoranaSpinGenerator =
      realMinkowskiMajorana (rindlerKillingGenerator X) := by
  obtain ⟨hT, hZ, hX, hY⟩ := rindlerBivector_commutators
  have hUnscaled :
      (realMajoranaTimeHead * realMajoranaSpaceTail) *
          realMinkowskiMajorana X -
        realMinkowskiMajorana X *
          (realMajoranaTimeHead * realMajoranaSpaceTail) =
        X.t • (-(2 : ℝ) • realMajoranaSpaceTail) +
          X.z • (-(2 : ℝ) • realMajoranaTimeHead) := by
    simp only [realMinkowskiMajorana, commutator_add_real_tensor,
      commutator_smul_real_tensor, hT, hZ, hX, hY]
    simp only [smul_zero, add_zero]
  calc
    _ = (- (1 / 2 : ℝ)) •
          ((realMajoranaTimeHead * realMajoranaSpaceTail) *
            realMinkowskiMajorana X -
           realMinkowskiMajorana X *
            (realMajoranaTimeHead * realMajoranaSpaceTail)) := by
          simp only [rindlerMajoranaSpinGenerator, rindlerMajoranaBivector]
          exact commutator_left_smul_real_tensor _ _ _
    _ = realMinkowskiMajorana ⟨X.z, 0, 0, X.t⟩ := by
          rw [hUnscaled]
          cases X with
          | mk t x y z =>
              simp [realMinkowskiMajorana, two_smul, smul_smul]
              module
    _ = realMinkowskiMajorana (rindlerKillingGenerator X) := by
          simp [rindlerKillingGenerator]

/-! ### Full real Lorentz Lie algebra on the Majorana CAR carrier

The real CAR owner already proves the bivector commutator formula for any
pair of Minkowski vectors.  This section specializes that formula to the six
coordinate planes of `(+---)` spacetime and packages their actual linear
combination as one element of the graded CAR algebra. -/

private def minkowskiTimeBasis :
    InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4 :=
  ⟨1, 0, 0, 0⟩

private def minkowskiXBasis :
    InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4 :=
  ⟨0, 1, 0, 0⟩

private def minkowskiYBasis :
    InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4 :=
  ⟨0, 0, 1, 0⟩

private def minkowskiZBasis :
    InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4 :=
  ⟨0, 0, 0, 1⟩

/-- The six-parameter real spin generator in the genuine three-mode
Koszul-graded CAR algebra.  Its coefficients multiply the six canonical
simple bivectors in the same `(tx, ty, tz, xy, xz, yz)` order used by
`lorentzGenerator4`. -/
def lorentzMajoranaSpinGenerator (btx bty btz rxy rxz ryz : ℝ) :
    realThreeMatrixGradedTensor :=
  btx • realMinkowskiBivector minkowskiTimeBasis minkowskiXBasis +
    bty • realMinkowskiBivector minkowskiTimeBasis minkowskiYBasis +
    btz • realMinkowskiBivector minkowskiTimeBasis minkowskiZBasis +
    rxy • realMinkowskiBivector minkowskiXBasis minkowskiYBasis +
    rxz • realMinkowskiBivector minkowskiXBasis minkowskiZBasis +
    ryz • realMinkowskiBivector minkowskiYBasis minkowskiZBasis

/-- The adjoint action of the six-component real Majorana spin generator is
exactly the existing six-component Lorentz infinitesimal on Minkowski
vectors.  This is a theorem on the noncommutative CAR carrier, not a
coordinate-only skewness statement. -/
theorem lorentzMajoranaSpinGenerator_commutator
    (btx bty btz rxy rxz ryz : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz *
        realMinkowskiMajorana X -
      realMinkowskiMajorana X *
        lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz =
      realMinkowskiMajorana
        (lorentzGenerator4 btx bty btz rxy rxz ryz X) := by
  simp only [lorentzMajoranaSpinGenerator, commutator_left_add_real_tensor,
    commutator_left_smul_real_tensor, realMinkowskiBivector_commutator]
  cases X with
  | mk t x y z =>
      simp [minkowskiTimeBasis, minkowskiXBasis, minkowskiYBasis,
        minkowskiZBasis, realMinkowskiMajorana, lorentzGenerator4]
      module

/-- The six-parameter Lorentz spin action also holds on the real
five-graded Fock carrier.  This is the explicit transport through the
existing real algebra equivalence from `8 × 8` Fock matrices to the
three-factor Koszul tensor of real `2 × 2` matrices; it connects the
Lorentz/Kosmann generator to the graded Fock lane without changing scalars
or replacing the operator product. -/
theorem lorentzMajoranaSpinGenerator_fock_commutator
    (btx bty btz rxy rxz ryz : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    fockMatrixToRealGradedTensor.symm
          (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) *
        fockMatrixToRealGradedTensor.symm (realMinkowskiMajorana X) -
      fockMatrixToRealGradedTensor.symm (realMinkowskiMajorana X) *
        fockMatrixToRealGradedTensor.symm
          (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) =
      fockMatrixToRealGradedTensor.symm
        (realMinkowskiMajorana
          (lorentzGenerator4 btx bty btz rxy rxz ryz X)) := by
  apply fockMatrixToRealGradedTensor.injective
  simp only [map_sub, map_mul, AlgEquiv.apply_symm_apply]
  exact lorentzMajoranaSpinGenerator_commutator btx bty btz rxy rxz ryz X

/-- The Lorentz inner derivation acts by the Leibniz rule on the associative
Jordan anticommutator that represents the nonassociative Peirce-supercolor
Jordan product.  This connects the real Lorentz/CAR action to the supercolor
Jordan lane while keeping the source product and the represented operator
product distinct. -/
theorem lorentzMajoranaAction_derives_supercolorJordan_image
    (btx bty btz rxy rxz ryz : ℝ)
    (U V : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra ℝ) :
    let B := lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz
    let R := InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode
    B * R (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.anticommutator U V) -
        R (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.anticommutator U V) * B =
      (B * R U - R U * B) * R V + R U * (B * R V - R V * B) +
        (B * R V - R V * B) * R U + R V * (B * R U - R U * B) := by
  let B := lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz
  let R := InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode
  dsimp only
  rw [InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge.supercolorJordanAnticommutator_in_tensor]
  change B * (R U * R V + R V * R U) - (R U * R V + R V * R U) * B = _
  noncomm_ring

/-! ### Rindler/Lipschitz flow on the exterior Plücker lane

The exterior owner uses the coordinate volume form on `ℝ⁴`, while the
spacetime owner uses signature `(+---)`.  The boost acts on the same ordered
coordinates `(t,x,y,z)`.  Its induced action on simple bivectors preserves
the Klein quadratic form because `cosh² - sinh² = 1`; this is a volume-form
statement and does not identify the Euclidean Klein form with the Minkowski
metric. -/

private def rindlerBoostPluckerVec4 (s : ℝ)
    (u : InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    InfoGeometry.Canonical.FierzKleinFoundation.Vec4 := fun i =>
  match i with
  | .t => Real.cosh s * u .t + Real.sinh s * u .z
  | .x => u .x
  | .y => u .y
  | .z => Real.sinh s * u .t + Real.cosh s * u .z

private def realSpacetimeToPluckerVec4
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    InfoGeometry.Canonical.FierzKleinFoundation.Vec4 := fun i =>
  match i with
  | .t => X.t
  | .x => X.x
  | .y => X.y
  | .z => X.z

/-- The physical Rindler boost is exactly the coordinate action used on the
exterior/Plücker carrier. -/
private theorem rindlerBoostPluckerVec4_realSpacetime
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) (s : ℝ) :
    rindlerBoostPluckerVec4 s (realSpacetimeToPluckerVec4 X) =
      realSpacetimeToPluckerVec4
        (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s) := by
  cases X with
  | mk t x y z =>
      funext i
      cases i <;> simp [rindlerBoostPluckerVec4, realSpacetimeToPluckerVec4,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost] <;> ring

/-- The boost preserves the Klein quadratic form on the Plücker bivector
formed by any two real spacetime vectors.  This gives an explicit
Souriau/Lipschitz-to-Plücker bridge on the decomposable locus. -/
theorem rindlerBoost_preserves_spacetime_wedge_kleinForm
    (s : ℝ)
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
        (InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4
          (realSpacetimeToPluckerVec4
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s))
          (realSpacetimeToPluckerVec4
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost Y s))) =
      InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
        (InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4
          (realSpacetimeToPluckerVec4 X) (realSpacetimeToPluckerVec4 Y)) := by
  rw [← rindlerBoostPluckerVec4_realSpacetime X s,
    ← rindlerBoostPluckerVec4_realSpacetime Y s]
  cases X with
  | mk xt xx xy xz =>
    cases Y with
    | mk yt yx yy yz =>
      unfold InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
        InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4
        rindlerBoostPluckerVec4 realSpacetimeToPluckerVec4
      nlinarith [Real.cosh_sq_sub_sinh_sq s]

/-- The induced action of a real Rindler boost on the six Plücker
coordinates.  This is the second exterior power of the boost on `Vec4`. -/
private def rindlerBoostPluckerCoordinateMap (s : ℝ) :
    (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun P := ![Real.cosh s * P 0 - Real.sinh s * P 4,
    Real.cosh s * P 1 - Real.sinh s * P 5, P 2, P 3,
    Real.cosh s * P 4 - Real.sinh s * P 0,
    Real.cosh s * P 5 - Real.sinh s * P 1]
  map_add' P Q := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c P := by
    funext i
    fin_cases i <;> simp <;> ring

private def rindlerBoostBivector (s : ℝ) :
    InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 →ₗ[ℝ]
      InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 :=
  InfoGeometry.Canonical.FierzKleinFoundation.bivector4CoordinateLinearEquiv.symm.toLinearMap.comp
    ((rindlerBoostPluckerCoordinateMap s).comp
      InfoGeometry.Canonical.FierzKleinFoundation.bivector4CoordinateLinearEquiv.toLinearMap)

/-- The exterior-square boost preserves the Klein quadratic form on every
bivector, including bivectors that are not decomposable. -/
theorem rindlerBoost_preserves_kleinForm
    (s : ℝ) (P : InfoGeometry.Canonical.FierzKleinFoundation.Bivector4) :
    InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
        (rindlerBoostBivector s P) =
      InfoGeometry.Canonical.FierzKleinFoundation.kleinForm P := by
  have hcosh : Real.cosh s ^ 2 - Real.sinh s ^ 2 = 1 := by
    simpa [pow_two] using Real.cosh_sq_sub_sinh_sq s
  cases P with
  | mk a b d e f g =>
    simp [rindlerBoostBivector, rindlerBoostPluckerCoordinateMap,
      InfoGeometry.Canonical.FierzKleinFoundation.bivector4CoordinateLinearEquiv,
      InfoGeometry.Canonical.FierzKleinFoundation.bivector4Coordinates,
      InfoGeometry.Canonical.FierzKleinFoundation.kleinForm]
    linear_combination (a * g - b * f) * hcosh

/-- Linear action induced on the literal exterior-square carrier by
conjugating the six-coordinate boost action through the owner's Plücker
equivalence. -/
def rindlerBoostExterior (s : ℝ) :
    (⋀[ℝ]^2 InfoGeometry.Canonical.FierzKleinFoundation.Vec4) →ₗ[ℝ]
      (⋀[ℝ]^2 InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :=
  InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv.symm.toLinearMap.comp
    ((rindlerBoostBivector s).comp
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv.toLinearMap)

/-- On simple bivectors, the linear exterior-square action is the wedge of
the boosted vectors. -/
theorem rindlerBoostExterior_ιMulti
    (s : ℝ) (u v : InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    rindlerBoostExterior s
        (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      exteriorPower.ιMulti ℝ 2
        ![rindlerBoostPluckerVec4 s u, rindlerBoostPluckerVec4 s v] := by
  apply InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv.injective
  change InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv
      (rindlerBoostExterior s (exteriorPower.ιMulti ℝ 2 ![u, v])) =
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv
      (exteriorPower.ιMulti ℝ 2
        ![rindlerBoostPluckerVec4 s u, rindlerBoostPluckerVec4 s v])
  simp only [rindlerBoostExterior, LinearMap.comp_apply,
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv_ιMulti]
  change InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv
      ((InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv).symm
        (rindlerBoostBivector s
          (InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv
            (exteriorPower.ιMulti ℝ 2 ![u, v])))) = _
  rw [InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv.apply_symm_apply]
  rw [InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv_ιMulti]
  have hcosh : Real.cosh s ^ 2 - Real.sinh s ^ 2 = 1 := by
    simpa [pow_two] using Real.cosh_sq_sub_sinh_sq s
  have hscale : 1 - Real.cosh s ^ 2 + Real.sinh s ^ 2 = 0 := by
    linarith [hcosh]
  -- The coordinate computation is exactly the six 2-by-2 minors.
  ext <;> simp [rindlerBoostBivector, rindlerBoostPluckerCoordinateMap,
    InfoGeometry.Canonical.FierzKleinFoundation.bivector4CoordinateLinearEquiv,
    InfoGeometry.Canonical.FierzKleinFoundation.bivector4Coordinates,
    InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4,
    rindlerBoostPluckerVec4] <;> try ring
  linear_combination
    (u InfoGeometry.Canonical.FierzKleinFoundation.I4.t *
      v InfoGeometry.Canonical.FierzKleinFoundation.I4.z -
    u InfoGeometry.Canonical.FierzKleinFoundation.I4.z *
      v InfoGeometry.Canonical.FierzKleinFoundation.I4.t) * hscale

/-- The induced map on the literal Mathlib exterior square preserves the
transported Klein form for arbitrary exterior bivectors. -/
theorem rindlerBoost_preserves_exteriorKleinForm
    (s : ℝ)
    (B : ⋀[ℝ]^2 InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
        (rindlerBoostExterior s B) =
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm B := by
  change InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
      (InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv
        (rindlerBoostExterior s B)) =
    InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
      (InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv B)
  simp only [rindlerBoostExterior, LinearMap.comp_apply]
  change InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
      (InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv
        ((InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv).symm
          (rindlerBoostBivector s
            (InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv B)))) = _
  rw [InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv.apply_symm_apply]
  exact rindlerBoost_preserves_kleinForm s _

/-- The real Lorentz spin lift is the restriction of the repository's
`LieActionLane` inner action on the complete three-factor CAR algebra.  It
acts on the Minkowski Majorana generators by the Lorentz infinitesimal and
satisfies Leibniz on every product of operators, not only on the vector
subspace. -/
theorem lorentzMajoranaSpinGenerator_lieActionLane
    (btx bty btz rxy rxz ryz : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let K := InfoGeometry.OperatorAlgebra.MaurerCartanTower.innerAlgLieActionLane
      ℝ realThreeMatrixGradedTensor
    K.operatorAction
        (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz)
        (realMinkowskiMajorana X) =
      realMinkowskiMajorana
        (lorentzGenerator4 btx bty btz rxy rxz ryz X) ∧
    ∀ a b : realThreeMatrixGradedTensor,
      K.operatorAction (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz)
          (a * b) =
        K.operatorAction (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) a * b +
          a * K.operatorAction (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) b := by
  let K := InfoGeometry.OperatorAlgebra.MaurerCartanTower.innerAlgLieActionLane
    ℝ realThreeMatrixGradedTensor
  constructor
  · simpa [K, InfoGeometry.OperatorAlgebra.MaurerCartanTower.innerAlgLieActionLane_operatorAction]
      using lorentzMajoranaSpinGenerator_commutator btx bty btz rxy rxz ryz X
  · intro a b
    simpa [K] using
      (InfoGeometry.OperatorAlgebra.MaurerCartanTower.innerAlgLieActionLane_isLeibniz
        ℝ realThreeMatrixGradedTensor
        (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) a b)

/-- The CAR anticommutator is invariant under the adjoint action of the
six-parameter spin generator.  This proves the Killing identity from the
actual associative three-factor graded carrier: the commutator is a
derivation, and the CAR anticommutator is the scalar Minkowski pairing. -/
theorem lorentzMajoranaSpinGenerator_preserves_CAR_metric
    (btx bty btz rxy rxz ryz : ℝ)
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    minkowski4Form (lorentzGenerator4 btx bty btz rxy rxz ryz X) Y +
      minkowski4Form X (lorentzGenerator4 btx bty btz rxy rxz ryz Y) = 0 := by
  let B := lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz
  let cX := realMinkowskiMajorana X
  let cY := realMinkowskiMajorana Y
  let GX := lorentzGenerator4 btx bty btz rxy rxz ryz X
  let GY := lorentzGenerator4 btx bty btz rxy rxz ryz Y
  have hX : B * cX - cX * B = realMinkowskiMajorana GX := by
    simpa [B, cX, GX] using
      lorentzMajoranaSpinGenerator_commutator btx bty btz rxy rxz ryz X
  have hY : B * cY - cY * B = realMinkowskiMajorana GY := by
    simpa [B, cY, GY] using
      lorentzMajoranaSpinGenerator_commutator btx bty btz rxy rxz ryz Y
  have hCARxy : cX * cY + cY * cX =
      (2 * minkowski4Form X Y) • (1 : realThreeMatrixGradedTensor) := by
    simpa [cX, cY, minkowski4Form] using
      realMinkowskiMajorana_anticommutator X Y
  have hCARgy : realMinkowskiMajorana GX * cY +
      cY * realMinkowskiMajorana GX =
        (2 * minkowski4Form GX Y) • (1 : realThreeMatrixGradedTensor) := by
    simpa [cY, minkowski4Form] using
      realMinkowskiMajorana_anticommutator GX Y
  have hCARxg : cX * realMinkowskiMajorana GY +
      realMinkowskiMajorana GY * cX =
        (2 * minkowski4Form X GY) • (1 : realThreeMatrixGradedTensor) := by
    simpa [cX, minkowski4Form] using
      realMinkowskiMajorana_anticommutator X GY
  have hCentral : B * (cX * cY + cY * cX) -
      (cX * cY + cY * cX) * B = 0 := by
    rw [hCARxy]
    simp
  have hPairing : B * (cX * cY + cY * cX) -
      (cX * cY + cY * cX) * B =
        (2 * (minkowski4Form GX Y + minkowski4Form X GY)) •
          (1 : realThreeMatrixGradedTensor) := by
    calc
      _ = (B * cX - cX * B) * cY + cX * (B * cY - cY * B) +
          (B * cY - cY * B) * cX + cY * (B * cX - cX * B) := by
            noncomm_ring
      _ = realMinkowskiMajorana GX * cY + cX * realMinkowskiMajorana GY +
          realMinkowskiMajorana GY * cX + cY * realMinkowskiMajorana GX := by
            rw [hX, hY]
      _ = (realMinkowskiMajorana GX * cY + cY * realMinkowskiMajorana GX) +
          (cX * realMinkowskiMajorana GY + realMinkowskiMajorana GY * cX) := by
            abel
      _ = _ := by rw [hCARgy, hCARxg]; module
  rw [hPairing] at hCentral
  have hOne : (1 : realThreeMatrixGradedTensor) ≠ 0 := by
    intro h
    have hMatrix := congrArg realThreeMatrixTensorToFin8 h
    simp at hMatrix
  have hScalar : 2 * (minkowski4Form GX Y + minkowski4Form X GY) = 0 := by
    exact (smul_eq_zero.mp hCentral).resolve_right hOne
  have hTwo : (2 : ℝ) ≠ 0 := by norm_num
  have hMetric : minkowski4Form GX Y + minkowski4Form X GY = 0 :=
    (mul_eq_zero.mp hScalar).resolve_left hTwo
  simpa [GX, GY] using hMetric

/-- Infinitesimal conformal action on real Majorana generators.  The scalar
term is a real dilation and the bivector term is the adjoint action in the
three-factor Koszul-graded matrix algebra. -/
def realConformalMajoranaAction
    (sigma btx bty btz rxy rxz ryz : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realThreeMatrixGradedTensor :=
  (2 * sigma) • realMinkowskiMajorana X +
    (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz *
        realMinkowskiMajorana X - realMinkowskiMajorana X *
        lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz)

/-- The real scalar-dilation-plus-bivector action is exactly the existing
conformal Lorentz generator on the `(1,3)` carrier, after applying the
Majorana representation. -/
theorem realConformalMajoranaAction_eq_conformalLorentzGenerator4
    (sigma btx bty btz rxy rxz ryz : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realConformalMajoranaAction sigma btx bty btz rxy rxz ryz X =
      realMinkowskiMajorana
        (conformalLorentzGenerator4 sigma btx bty btz rxy rxz ryz X) := by
  rw [realConformalMajoranaAction, lorentzMajoranaSpinGenerator_commutator]
  cases X with
  | mk t x y z =>
    simp [realMinkowskiMajorana, conformalLorentzGenerator4,
      lorentzGenerator4, add_smul, smul_add]
    module

/-- The real conformal CAR action scales the Majorana anticommutator by the
expected infinitesimal conformal factor.  This is the operator-algebra form
of the conformal Killing identity: the bivector commutator preserves the
CAR pairing, while the real dilation contributes `8 * sigma` to the
anticommutator normalization. -/
theorem realConformalMajoranaAction_CAR_anticommutator_derivative
    (sigma btx bty btz rxy rxz ryz : ℝ)
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realConformalMajoranaAction sigma btx bty btz rxy rxz ryz X *
        realMinkowskiMajorana Y +
      realMinkowskiMajorana Y *
        realConformalMajoranaAction sigma btx bty btz rxy rxz ryz X +
      realMinkowskiMajorana X *
        realConformalMajoranaAction sigma btx bty btz rxy rxz ryz Y +
      realConformalMajoranaAction sigma btx bty btz rxy rxz ryz Y *
        realMinkowskiMajorana X =
      (8 * sigma * minkowski4Form X Y) • (1 : realThreeMatrixGradedTensor) := by
  let B := lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz
  let cX := realMinkowskiMajorana X
  let cY := realMinkowskiMajorana Y
  have hCAR : cX * cY + cY * cX =
      (2 * minkowski4Form X Y) • (1 : realThreeMatrixGradedTensor) := by
    simpa [cX, cY, minkowski4Form] using realMinkowskiMajorana_anticommutator X Y
  have hCentral : B * (cX * cY + cY * cX) - (cX * cY + cY * cX) * B = 0 := by
    rw [hCAR]
    simp
  have hDilation :
      (2 * sigma) • cX * cY + cY * ((2 * sigma) • cX) +
        cX * ((2 * sigma) • cY) + (2 * sigma) • cY * cX =
      (4 * sigma) • (cX * cY + cY * cX) := by
    simp only [smul_mul_assoc, mul_smul_comm]
    module
  have hAdjoint :
      (B * cX - cX * B) * cY + cY * (B * cX - cX * B) +
        cX * (B * cY - cY * B) + (B * cY - cY * B) * cX =
      B * (cX * cY + cY * cX) - (cX * cY + cY * cX) * B := by
    noncomm_ring
  calc
    _ = ((2 * sigma) • cX * cY + cY * ((2 * sigma) • cX) +
          cX * ((2 * sigma) • cY) + (2 * sigma) • cY * cX) +
        ((B * cX - cX * B) * cY + cY * (B * cX - cX * B) +
          cX * (B * cY - cY * B) + (B * cY - cY * B) * cX) := by
          simp only [realConformalMajoranaAction, B, cX, cY, smul_mul_assoc,
            mul_smul_comm, sub_mul, mul_sub, add_mul, mul_add]
          noncomm_ring
    _ = (4 * sigma) • (cX * cY + cY * cX) +
        (B * (cX * cY + cY * cX) - (cX * cY + cY * cX) * B) := by
          rw [hDilation, hAdjoint]
    _ = (4 * sigma) • (cX * cY + cY * cX) := by rw [hCentral]; simp
    _ = (8 * sigma * minkowski4Form X Y) •
        (1 : realThreeMatrixGradedTensor) := by
          rw [hCAR, smul_smul]
          congr 1
          ring

/-- The full real Lorentz spin action remains valid after transport to the
existing doubled-Krein endomorphism carrier. -/
theorem lorentzMajoranaSpinGenerator_onKrein_commutator
    (btx bty btz rxy rxz ryz : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realThreeMatrixTensorOnH4
        (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) -
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
        realThreeMatrixTensorOnH4
          (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) =
      realThreeMatrixTensorOnH4
        (realMinkowskiMajorana
          (lorentzGenerator4 btx bty btz rxy rxz ryz X)) := by
  calc
    _ = realThreeMatrixTensorOnH4
        (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz *
          realMinkowskiMajorana X - realMinkowskiMajorana X *
          lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) := by
          rw [map_sub, map_mul, map_mul]
    _ = _ := congrArg realThreeMatrixTensorOnH4
      (lorentzMajoranaSpinGenerator_commutator btx bty btz rxy rxz ryz X)

/-- The increment of Souriau's affine inverse-temperature field is the
commutator action of the corresponding real Majorana spin generator.  The
constant inverse-temperature offset cancels, while the Lorentz-linear part
is represented on the actual CAR algebra. -/
theorem affineLorentzTemperatureField_increment_eq_majorana_commutator
    (btx bty btz rxy rxz ryz : ℝ)
    (c X h : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realMinkowskiMajorana
        (affineLorentzTemperatureField4 btx bty btz rxy rxz ryz c
          ⟨X.t + h.t, X.x + h.x, X.y + h.y, X.z + h.z⟩) =
      realMinkowskiMajorana
          (affineLorentzTemperatureField4 btx bty btz rxy rxz ryz c X) +
        (lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz *
            realMinkowskiMajorana h -
          realMinkowskiMajorana h *
            lorentzMajoranaSpinGenerator btx bty btz rxy rxz ryz) := by
  rw [lorentzMajoranaSpinGenerator_commutator]
  cases c with
  | mk ct cx cy cz =>
    cases X with
    | mk xt xx xy xz =>
      cases h with
      | mk ht hx hy hz =>
        simp [affineLorentzTemperatureField4, lorentzGenerator4,
          realMinkowskiMajorana, add_smul]
        module

/-- The infinitesimal real CAR boost generator acts on the doubled-Krein
carrier by the represented Souriau Rindler Killing vector. -/
theorem rindlerMajoranaSpinGenerator_onKrein_commutator
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realThreeMatrixTensorOnH4 rindlerMajoranaSpinGenerator *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) -
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
        realThreeMatrixTensorOnH4 rindlerMajoranaSpinGenerator =
      realThreeMatrixTensorOnH4
        (realMinkowskiMajorana (rindlerKillingGenerator X)) := by
  calc
    _ = realThreeMatrixTensorOnH4
        (rindlerMajoranaSpinGenerator * realMinkowskiMajorana X -
          realMinkowskiMajorana X * rindlerMajoranaSpinGenerator) := by
          rw [map_sub, map_mul, map_mul]
    _ = _ := congrArg realThreeMatrixTensorOnH4
      (rindlerMajoranaSpinGenerator_commutator X)

/-- The CAR spin-generator commutator is the directional increment of the
existing affine Rindler inverse-temperature field. The offset `b` and base
point `X` cancel in the increment; this theorem records the Souriau/CAR link
on the concrete flat model without asserting a general curved equilibrium
criterion. -/
theorem rindlerMajoranaSpinGenerator_eq_inverseTemperatureIncrement
    (b X H : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    rindlerMajoranaSpinGenerator * realMinkowskiMajorana H -
        realMinkowskiMajorana H * rindlerMajoranaSpinGenerator =
      realMinkowskiMajorana ⟨
        (rindlerInverseTemperatureField b
          ⟨X.t + H.t, X.x + H.x, X.y + H.y, X.z + H.z⟩).t -
            (rindlerInverseTemperatureField b X).t,
        (rindlerInverseTemperatureField b
          ⟨X.t + H.t, X.x + H.x, X.y + H.y, X.z + H.z⟩).x -
            (rindlerInverseTemperatureField b X).x,
        (rindlerInverseTemperatureField b
          ⟨X.t + H.t, X.x + H.x, X.y + H.y, X.z + H.z⟩).y -
            (rindlerInverseTemperatureField b X).y,
        (rindlerInverseTemperatureField b
          ⟨X.t + H.t, X.x + H.x, X.y + H.y, X.z + H.z⟩).z -
            (rindlerInverseTemperatureField b X).z⟩ := by
  rw [rindlerMajoranaSpinGenerator_commutator]
  cases b with
  | mk bt bx by_ bz =>
    cases X with
    | mk xt xx xy xz =>
      cases H with
      | mk ht hx hy hz =>
        simp [rindlerInverseTemperatureField, rindlerKillingGenerator,
          realMinkowskiMajorana]

/-- The CAR rotor action is the real four-dimensional lift of the
repository's existing `Cl(1,1)` spin-group action: the spin-group element acts
on the `(t,z)` plane, and the two transverse coordinates are retained. This
identifies the actual CAR sandwich with the established real spin-group
isometry after applying the physical vector contraction. -/
theorem rindlerMajoranaSpinRotor_eq_cl11SpinGroupAction
    (s : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    rindlerMajoranaSpinRotor s * realMinkowskiMajorana X *
        rindlerMajoranaSpinRotorReverse s =
      realMinkowskiMajorana
        ⟨(InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.spinGroupToIsometryHom
            InfoGeometry.Clifford.Cl11Matrix.q11
            ⟨InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor (-s / 2),
              InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩
            (X.t, X.z)).1,
          X.x,
          X.y,
          (InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.spinGroupToIsometryHom
            InfoGeometry.Clifford.Cl11Matrix.q11
            ⟨InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor (-s / 2),
              InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor_mem_spinGroup (-s / 2)⟩
            (X.t, X.z)).2⟩ := by
  rw [rindlerMajoranaSpinRotor_sandwich]
  apply congrArg realMinkowskiMajorana
  cases X with
  | mk t x y z =>
      rw [cl11SpinGroupAction_eq_boostFlow]
      ext <;> simp [boostFlow,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost] <;> ring_nf

/-- The finite CAR rotor action on the physical Majorana contraction is the
same action as the corresponding element of Mathlib's real `Cl(1,1)`
Lipschitz group. This identifies the operator-side Majorana flow directly
with the Souriau/Lipschitz spacetime action, retaining the two transverse
coordinates. -/
theorem rindlerMajoranaSpinRotor_eq_cl11LipschitzGroupAction
    (s : ℝ)
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let action :=
      InfoGeometry.Clifford.LipschitzWittRieszPrimary.lipschitzGroupToIsometryHom
        InfoGeometry.Clifford.Cl11Matrix.q11
        ⟨_root_.pinGroup.toUnits
            (⟨InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor (-s / 2),
              _root_.spinGroup.mem_pin
                (InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor_mem_spinGroup (-s / 2))⟩ :
              _root_.pinGroup InfoGeometry.Clifford.Cl11Matrix.q11),
          _root_.pinGroup.units_mem_lipschitzGroup
            (⟨InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor (-s / 2),
              _root_.spinGroup.mem_pin
                (InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.cl11HyperbolicRotor_mem_spinGroup (-s / 2))⟩ :
              _root_.pinGroup InfoGeometry.Clifford.Cl11Matrix.q11).2⟩ (X.t, X.z)
    rindlerMajoranaSpinRotor s * realMinkowskiMajorana X *
        rindlerMajoranaSpinRotorReverse s =
      realMinkowskiMajorana ⟨action.1, X.x, X.y, action.2⟩ := by
  dsimp only
  rw [rindlerMajoranaSpinRotor_sandwich]
  apply congrArg realMinkowskiMajorana
  cases X with
  | mk t x y z =>
      rw [cl11LipschitzAction_eq_boostFlow]
      ext <;> simp [boostFlow,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost] <;> ring

/-! ### Weyl soldering and the real three-mode Majorana contraction

The circular Yang--Mills owner uses two Weyl blocks over `ℂ`, while the
Hestenes/CAR owner uses the real Koszul tensor of three `M₂(ℝ)` factors.  We
identify the shared real Minkowski vector by duplicating its four coordinates
on the two circular sheets, then compare the squares after realification on
`KreinFrame4`.  This is a quadratic Clifford comparison; it does not assert
an equality of the two unsquared matrix representations or use `ℂ` as scalar
field on the doubled carrier.
-/

/-- Put a physical real `(1,3)` vector into both circular chiral sheets. -/
def realMinkowskiCircularCoordinate
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    Coordinate := ![X.t, X.x, X.y, X.z, X.t, X.x, X.y, X.z]

/-- The duplicated circular Witt norm is the physical real Minkowski interval. -/
theorem realMinkowskiCircularCoordinate_wittNorm
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm
        (realMinkowskiCircularCoordinate X) =
      InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X := by
  cases X with
  | mk t x y z =>
      simp [realMinkowskiCircularCoordinate,
        InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm,
        InfoGeometry.Canonical.RealSpacetime4x4Closure.interval]; ring

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
      simp
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

/-- The trace of the real endomorphism on the doubled Krein carrier is the
realified matrix trace.  The trace is computed on the actual `KreinFrame4`
endomorphism, using the existing coordinate equivalence and realification
theorem. -/
theorem realifiedCircularMatrixEnd_trace (A : Matrix (Fin 4) (Fin 4) ℂ) :
    LinearMap.trace ℝ KreinFrame4 (realifiedCircularMatrixEnd A) =
      2 * (Matrix.trace A).re := by
  calc
    LinearMap.trace ℝ KreinFrame4 (realifiedCircularMatrixEnd A) =
        LinearMap.trace ℝ (Fin 4 ⊕ Fin 4 → ℝ)
          (Matrix.toLinAlgEquiv'
            (InfoGeometry.Quantum.Realification.realify A)) := by
          change LinearMap.trace ℝ KreinFrame4
              ((realificationKreinFrameEquiv.conjAlgEquiv ℝ)
                (Matrix.toLinAlgEquiv'
                  (InfoGeometry.Quantum.Realification.realify A))) = _
          exact LinearMap.trace_conj' _ realificationKreinFrameEquiv
    _ = Matrix.trace (InfoGeometry.Quantum.Realification.realify A) := by
          have hlin :
              Matrix.toLinAlgEquiv'
                  (InfoGeometry.Quantum.Realification.realify A) =
                (InfoGeometry.Quantum.Realification.realify A).toLin' := by
            ext v
            simp [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
          rw [hlin, Matrix.trace_toLin'_eq]
    _ = 2 * (Matrix.trace A).re :=
          InfoGeometry.Quantum.Realification.trace_realify A

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

/-- The Hilbert–Schmidt action of the circular Yang–Mills curvature, read as
the trace of its realified operator product on `KreinFrame4`, is twice the
complex-matrix action and hence has the explicit real value shown.  This
transports the existing action theorem to the real doubled carrier; it does
not identify the Euclidean adjoint with the Krein adjoint. -/
theorem realifiedCircularCurvatureMat4_hilbertSchmidt_action (x : Coordinate) :
    LinearMap.trace ℝ KreinFrame4
        (realifiedCircularMatrixEnd
          ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x)) =
      8 * (InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm x ^ 2 +
        normSq3 (chiralBoostVec x) +
        normSq3 (chiralVorticityVec x)) := by
  rw [realifiedCircularMatrixEnd_trace,
    circularCurvatureMat4_hilbertSchmidt_action]
  simp only [Complex.ofReal_re]
  ring

/-- The same circular curvature action is the trace of the product of the
two corresponding operators in the existing real three-mode CAR algebra:
the first CAR element represents the realification of the source adjoint,
and the second represents the realified curvature.  The owner equivalence
then acts on the actual `KreinFrame4` carrier. -/
theorem realCAR_circularCurvatureMat4_hilbertSchmidt_action (x : Coordinate) :
    LinearMap.trace ℝ KreinFrame4
        (realThreeMatrixTensorOnH4
          (realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd ((circularCurvatureMat4 x)ᴴ)) *
            realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd (circularCurvatureMat4 x)))) =
      8 * (InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm x ^ 2 +
        normSq3 (chiralBoostVec x) + normSq3 (chiralVorticityVec x)) := by
  have hrep :
      realThreeMatrixTensorOnH4
          (realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd ((circularCurvatureMat4 x)ᴴ)) *
            realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd (circularCurvatureMat4 x))) =
        realifiedCircularMatrixEnd
          ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x) := by
    rw [map_mul, realThreeMatrixTensorOnH4.apply_symm_apply,
      realThreeMatrixTensorOnH4.apply_symm_apply,
      realifiedCircularMatrixEnd_mul]
  rw [hrep]
  exact realifiedCircularCurvatureMat4_hilbertSchmidt_action x

/-- On the real doubled carrier, the difference between the realified
Hilbert–Schmidt curvature action and the realified quadratic curvature trace
is exactly twice the source vorticity gap. -/
theorem realifiedCircularCurvatureMat4_vorticity_action_gap (x : Coordinate) :
    LinearMap.trace ℝ KreinFrame4
        (realifiedCircularMatrixEnd
          ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x)) -
      LinearMap.trace ℝ KreinFrame4
        (realifiedCircularMatrixEnd
          (circularCurvatureMat4 x * circularCurvatureMat4 x)) =
      16 * normSq3 (chiralVorticityVec x) := by
  rw [realifiedCircularMatrixEnd_trace, realifiedCircularMatrixEnd_trace]
  have h := congrArg Complex.re (circularCurvatureMat4_vorticity_action_gap x)
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  calc
    2 * ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace.re -
        2 * (circularCurvatureMat4 x * circularCurvatureMat4 x).trace.re =
        2 * (((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace.re -
          (circularCurvatureMat4 x * circularCurvatureMat4 x).trace.re) := by ring
    _ = 2 * (8 * normSq3 (chiralVorticityVec x)) := by rw [h]
    _ = 16 * normSq3 (chiralVorticityVec x) := by ring

/-- The vorticity action gap is the same ordered-trace difference when both
curvature products are represented in the existing real three-mode CAR
endomorphism algebra on `KreinFrame4`. This is an operator-trace transport
through the actual algebra equivalence; it does not identify the CAR mass
spectral gap with the Yang--Mills action gap. -/
theorem realCAR_circularCurvatureMat4_vorticity_action_gap (x : Coordinate) :
    LinearMap.trace ℝ KreinFrame4
        (realThreeMatrixTensorOnH4
          (realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd ((circularCurvatureMat4 x)ᴴ)) *
            realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd (circularCurvatureMat4 x)))) -
      LinearMap.trace ℝ KreinFrame4
        (realThreeMatrixTensorOnH4
          (realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd (circularCurvatureMat4 x)) *
            realThreeMatrixTensorOnH4.symm
              (realifiedCircularMatrixEnd (circularCurvatureMat4 x)))) =
      16 * normSq3 (chiralVorticityVec x) := by
  have hprod (A B : Matrix (Fin 4) (Fin 4) ℂ) :
      realThreeMatrixTensorOnH4
          (realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd A) *
            realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd B)) =
        realifiedCircularMatrixEnd (A * B) := by
    rw [map_mul, realThreeMatrixTensorOnH4.apply_symm_apply,
      realThreeMatrixTensorOnH4.apply_symm_apply,
      realifiedCircularMatrixEnd_mul]
  rw [hprod, hprod]
  exact realifiedCircularCurvatureMat4_vorticity_action_gap x

@[simp] theorem realifiedCircularMatrixEnd_add
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    realifiedCircularMatrixEnd (A + B) =
      realifiedCircularMatrixEnd A + realifiedCircularMatrixEnd B := by
  simp [realifiedCircularMatrixEnd, InfoGeometry.Quantum.Realification.realify_add]

@[simp] theorem realifiedCircularMatrixEnd_one :
    realifiedCircularMatrixEnd (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  simp [realifiedCircularMatrixEnd, InfoGeometry.Quantum.Realification.realify_one]

@[simp] theorem realifiedCircularMatrixEnd_sub
    (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    realifiedCircularMatrixEnd (A - B) =
      realifiedCircularMatrixEnd A - realifiedCircularMatrixEnd B := by
  simp [sub_eq_add_neg, realifiedCircularMatrixEnd]

/-! ### Constructive rest-frame supercharges from the real CAR owner

The stored chiral presentation records an operator equation but does not
construct its charges. Here a genuine pair is constructed from the existing
real three-mode CAR annihilation/creation operators. At rest, the spinor
momentum is the scalar matrix `E I`; the result proves its operator
anticommutator on the actual doubled real Krein carrier. This is a rest-frame
construction and makes no claim of a general positive-momentum square-root or
Lorentz-covariant charge doublet.
-/

/-- The real rest-frame annihilation charge, obtained by scaling the existing
head CAR annihilator by `sqrt (2E)`. -/
def realRestFrameAnnihilationCharge (E : ℝ) :
    Module.End ℝ KreinFrame4 :=
  Real.sqrt (2 * E) • realThreeMatrixTensorOnH4 realThreeAnnihilationHead

/-- The real rest-frame creation partner, obtained from the existing head CAR
creator with the same real coefficient. -/
def realRestFrameCreationCharge (E : ℝ) :
    Module.End ℝ KreinFrame4 :=
  Real.sqrt (2 * E) • realThreeMatrixTensorOnH4 realThreeCreationHead

private lemma realSmul_mul_realSmul_local {A : Type*} [Ring A] [Algebra ℝ A]
    (r s : ℝ) (a b : A) :
    (r • a) * (s • b) = (r * s) • (a * b) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm s r]

/-- For nonnegative rest energy, the constructed real CAR charge pair has
operator anticommutator `2E` times the identity on the doubled Krein carrier.
The proof uses the established head-mode CAR relation. -/
theorem realRestFrameCARCharges_anticommutator
    (E : ℝ) (hE : 0 ≤ E) :
    realRestFrameAnnihilationCharge E * realRestFrameCreationCharge E +
      realRestFrameCreationCharge E * realRestFrameAnnihilationCharge E =
        (2 * E) • (1 : Module.End ℝ KreinFrame4) := by
  have hroot : Real.sqrt (2 * E) * Real.sqrt (2 * E) = 2 * E := by
    rw [← pow_two, Real.sq_sqrt (mul_nonneg (by norm_num) hE)]
  rw [realRestFrameAnnihilationCharge,
    realRestFrameCreationCharge,
    realSmul_mul_realSmul_local, realSmul_mul_realSmul_local,
    ← smul_add, realThreeMatrixTensorOnH4_head_CAR, hroot]

/-- The sum of the constructed charge pair is the scaled existing real time
Majorana operator on the doubled Krein carrier. -/
theorem realRestFrameCARCharges_sum_eq_timeMajorana (E : ℝ) :
    realRestFrameAnnihilationCharge E + realRestFrameCreationCharge E =
      Real.sqrt (2 * E) •
        realThreeMatrixTensorOnH4 realMajoranaTimeHead := by
  simp [realRestFrameAnnihilationCharge, realRestFrameCreationCharge,
    realMajoranaTimeHead, map_add]

/-- Their difference is the scaled existing real space Majorana operator in
the same first graded matrix factor. -/
theorem realRestFrameCARCharges_sub_eq_spaceMajorana (E : ℝ) :
    realRestFrameAnnihilationCharge E - realRestFrameCreationCharge E =
      Real.sqrt (2 * E) •
        realThreeMatrixTensorOnH4 realMajoranaSpaceHead := by
  simp [realRestFrameAnnihilationCharge, realRestFrameCreationCharge,
    realMajoranaSpaceHead, map_sub]
  module

/-- The realified circular chiral connection and the real graded-tensor
Majorana slash have identical squares on the doubled Krein carrier. Both
sides equal the Minkowski interval times the identity endomorphism. -/
theorem realifiedCircularWeyl_majorana_square
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) *
        realifiedCircularMatrixEnd
          (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) =
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) := by
  have hWeyl :
      circularConnectionMat4 (realMinkowskiCircularCoordinate X) *
          circularConnectionMat4 (realMinkowskiCircularCoordinate X) =
        ((InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X : ℝ) : ℂ) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [circularConnectionMat4, chiralOffBlock4_mul]
    have hUL' : weylUpperMat (realMinkowskiCircularCoordinate X) *
          weylLowerMat (realMinkowskiCircularCoordinate X) =
        ((InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [weylUpperMat_mul_weylLowerMat]
      cases X with
      | mk t x y z =>
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [realMinkowskiCircularCoordinate, chiralBoostVec,
              chiralVorticityVec,
              InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm,
              InfoGeometry.Canonical.RealSpacetime4x4Closure.interval,
              solder, σ0, σ1, σ2, σ3] <;> ring
    have hLU' : weylLowerMat (realMinkowskiCircularCoordinate X) *
          weylUpperMat (realMinkowskiCircularCoordinate X) =
        ((InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [weylLowerMat_mul_weylUpperMat]
      cases X with
      | mk t x y z =>
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [realMinkowskiCircularCoordinate, chiralBoostVec,
              chiralVorticityVec,
              InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge.wittNorm,
              InfoGeometry.Canonical.RealSpacetime4x4Closure.interval,
              solder, σ0, σ1, σ2, σ3] <;> ring
    rw [hUL', hLU']
    cases X with
    | mk t x y z =>
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [chiralDiagBlock4, Matrix.smul_apply,
            InfoGeometry.Canonical.RealSpacetime4x4Closure.interval]
  calc
    _ = realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate X) *
          circularConnectionMat4 (realMinkowskiCircularCoordinate X)) := by
            rw [realifiedCircularMatrixEnd_mul]
    _ = InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X •
          (1 : Module.End ℝ KreinFrame4) := by
            rw [hWeyl]
            simp [realifiedCircularMatrixEnd]
    _ = realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
          realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) := by
            symm
            exact realMinkowskiMajorana_onKrein_square X

/-- The circular Weyl quadratic connection is covariant under the same real
Rindler CAR rotor on the doubled Krein carrier. This composes the circular
Weyl/Majorana square identification with the actual CAR sandwich action and
uses the reverse-rotor identity; it is an operator covariance theorem, not
an equality of the unsquared Weyl and Majorana representations. -/
theorem realifiedCircularWeyl_square_rindler_covariant
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (s : ℝ) :
    realifiedCircularMatrixEnd
        (circularConnectionMat4
          (realMinkowskiCircularCoordinate
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s))) ^ 2 =
      realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
        (realifiedCircularMatrixEnd
          (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) ^ 2) *
        realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) := by
  have hRev :
      realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) *
          realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) = 1 := by
    have hSourceComm :
        rindlerMajoranaSpinRotorReverse s * rindlerMajoranaSpinRotor s =
          rindlerMajoranaSpinRotor s * rindlerMajoranaSpinRotorReverse s := by
      simp only [rindlerMajoranaSpinRotor, rindlerMajoranaSpinRotorReverse]
      noncomm_ring
      module
    rw [← map_mul, hSourceComm,
      rindlerMajoranaSpinRotor_mul_reverse, map_one]
  calc
    _ = realThreeMatrixTensorOnH4
          (realMinkowskiMajorana
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s)) ^ 2 :=
          realifiedCircularWeyl_majorana_square _
    _ = (realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
          realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
          realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s)) ^ 2 := by
          rw [rindlerMajoranaSpinRotor_onKrein_sandwich]
    _ = realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
          (realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) ^ 2) *
          realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) := by
          rw [pow_two]
          calc
            _ = realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
                realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
                (realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) *
                  realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s)) *
                realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
                realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) := by
                  noncomm_ring
            _ = _ := by rw [hRev]; noncomm_ring
    _ = realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
          (realifiedCircularMatrixEnd
            (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) ^ 2) *
          realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) := by
          rw [pow_two, ← realifiedCircularWeyl_majorana_square X]
          rw [pow_two]

/-- The realified circular Yang--Mills curvature itself transforms by the
same doubled-Krein CAR rotor as the connection square. This is the
owner-level curvature statement obtained from the existing identity
`curvature = connection * connection`; no new curvature operator or matrix
carrier is introduced. -/
theorem realifiedCircularCurvature_rindler_covariant
    (X : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (s : ℝ) :
    realifiedCircularMatrixEnd
        (circularCurvatureMat4
          (realMinkowskiCircularCoordinate
            (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s))) =
      realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
        realifiedCircularMatrixEnd
          (circularCurvatureMat4 (realMinkowskiCircularCoordinate X)) *
        realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) := by
  calc
    _ = realifiedCircularMatrixEnd
          (circularConnectionMat4
            (realMinkowskiCircularCoordinate
              (InfoGeometry.Canonical.RealSpacetime4x4Closure.rindler_boost X s))) ^ 2 :=
          realifiedCircularCurvature_eq_connection_square _
    _ = realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
          realifiedCircularMatrixEnd
            (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) ^ 2 *
          realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) :=
          realifiedCircularWeyl_square_rindler_covariant X s
    _ = realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotor s) *
          realifiedCircularMatrixEnd
            (circularCurvatureMat4 (realMinkowskiCircularCoordinate X)) *
          realThreeMatrixTensorOnH4 (rindlerMajoranaSpinRotorReverse s) := by
          rw [realifiedCircularCurvature_eq_connection_square
            (realMinkowskiCircularCoordinate X)]
          rw [pow_two]

/-- The two real Clifford realizations have the same polarized bilinear
operator relation, not only the same vector squares.  Thus their symmetric
operator product on any pair of real Minkowski vectors is identical on the
existing doubled Krein carrier.  This is a genuine compatibility of the
circular Weyl and three-mode Majorana representations; it does not assert
equality of the individual slash operators or identify the Peirce translation
generator with a Majorana generator. -/
private def realSpacetimeAdd
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4 :=
  ⟨X.t + Y.t, X.x + Y.x, X.y + Y.y, X.z + Y.z⟩

private lemma anticommutator_eq_square_sub {A : Type*} [Ring A] (a b : A) :
    a * b + b * a = (a + b) * (a + b) - a * a - b * b := by
  noncomm_ring

private theorem weylUpperMat_add (x y : Coordinate) :
    weylUpperMat (x + y) = weylUpperMat x + weylUpperMat y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylUpperMat,
      InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge.pauliSolder2x2,
      InfoGeometry.Quantum.PauliSoldering.solder,
      InfoGeometry.Quantum.PauliSoldering.σ0,
      InfoGeometry.Quantum.PauliSoldering.σ1,
      InfoGeometry.Quantum.PauliSoldering.σ2,
      InfoGeometry.Quantum.PauliSoldering.σ3] <;> ring

private theorem weylLowerMat_add (x y : Coordinate) :
    weylLowerMat (x + y) = weylLowerMat x + weylLowerMat y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylLowerMat,
      InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge.pauliSolder2x2,
      InfoGeometry.Quantum.PauliSoldering.solder,
      InfoGeometry.Quantum.PauliSoldering.σ0,
      InfoGeometry.Quantum.PauliSoldering.σ1,
      InfoGeometry.Quantum.PauliSoldering.σ2,
      InfoGeometry.Quantum.PauliSoldering.σ3] <;> ring

private theorem chiralOffBlock4_add {R : Type*} [Ring R]
    (u₁ u₂ l₁ l₂ : Matrix (Fin 2) (Fin 2) R) :
    chiralOffBlock4 (u₁ + u₂) (l₁ + l₂) =
      chiralOffBlock4 u₁ l₁ + chiralOffBlock4 u₂ l₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

private theorem circularConnectionMat4_add (x y : Coordinate) :
    circularConnectionMat4 (x + y) =
      circularConnectionMat4 x + circularConnectionMat4 y := by
  change chiralOffBlock4 (weylUpperMat (x + y)) (weylLowerMat (x + y)) =
    chiralOffBlock4 (weylUpperMat x) (weylLowerMat x) +
      chiralOffBlock4 (weylUpperMat y) (weylLowerMat y)
  rw [weylUpperMat_add, weylLowerMat_add, chiralOffBlock4_add]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem realifiedCircularWeyl_majorana_polarization
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    let circularSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
      realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate Z))
    let majoranaSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana Z)
    circularSlash X * circularSlash Y + circularSlash Y * circularSlash X =
      majoranaSlash X * majoranaSlash Y + majoranaSlash Y * majoranaSlash X := by
  dsimp
  let circularSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
    realifiedCircularMatrixEnd
      (circularConnectionMat4 (realMinkowskiCircularCoordinate Z))
  let majoranaSlash (Z : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :=
    realThreeMatrixTensorOnH4 (realMinkowskiMajorana Z)
  have hCircularAdd (U V :
      InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
      circularSlash (realSpacetimeAdd U V) = circularSlash U + circularSlash V := by
    dsimp [circularSlash]
    have hConn : circularConnectionMat4
        (realMinkowskiCircularCoordinate (realSpacetimeAdd U V)) =
        circularConnectionMat4 (realMinkowskiCircularCoordinate U) +
          circularConnectionMat4 (realMinkowskiCircularCoordinate V) := by
      cases U with
      | mk ut ux uy uz =>
        cases V with
        | mk vt vx vy vz =>
          have hcoord :
              realMinkowskiCircularCoordinate
                  (realSpacetimeAdd ⟨ut, ux, uy, uz⟩ ⟨vt, vx, vy, vz⟩) =
                realMinkowskiCircularCoordinate ⟨ut, ux, uy, uz⟩ +
                  realMinkowskiCircularCoordinate ⟨vt, vx, vy, vz⟩ := by
            funext i
            fin_cases i <;> rfl
          rw [hcoord, circularConnectionMat4_add]
    rw [hConn, realifiedCircularMatrixEnd_add]
  have hMajoranaAdd (U V :
      InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
      majoranaSlash (realSpacetimeAdd U V) = majoranaSlash U + majoranaSlash V := by
    dsimp [majoranaSlash]
    cases U with
    | mk ut ux uy uz =>
      cases V with
      | mk vt vx vy vz =>
        have hMajorana :
            realMinkowskiMajorana (realSpacetimeAdd ⟨ut, ux, uy, uz⟩
                ⟨vt, vx, vy, vz⟩) =
              realMinkowskiMajorana ⟨ut, ux, uy, uz⟩ +
                realMinkowskiMajorana ⟨vt, vx, vy, vz⟩ := by
          simp only [realMinkowskiMajorana, realSpacetimeAdd, add_smul]
          abel
        calc
          _ = realThreeMatrixTensorOnH4
              (realMinkowskiMajorana ⟨ut, ux, uy, uz⟩ +
                realMinkowskiMajorana ⟨vt, vx, vy, vz⟩) :=
                congrArg realThreeMatrixTensorOnH4 hMajorana
          _ = _ := map_add _ _ _
  calc
    circularSlash X * circularSlash Y + circularSlash Y * circularSlash X =
        (circularSlash X + circularSlash Y) * (circularSlash X + circularSlash Y) -
          circularSlash X * circularSlash X - circularSlash Y * circularSlash Y :=
      anticommutator_eq_square_sub _ _
    _ = circularSlash (realSpacetimeAdd X Y) * circularSlash (realSpacetimeAdd X Y) -
          circularSlash X * circularSlash X - circularSlash Y * circularSlash Y := by
      rw [← hCircularAdd]
    _ = majoranaSlash (realSpacetimeAdd X Y) * majoranaSlash (realSpacetimeAdd X Y) -
          majoranaSlash X * majoranaSlash X - majoranaSlash Y * majoranaSlash Y := by
      rw [realifiedCircularWeyl_majorana_square]
      rw [realifiedCircularWeyl_majorana_square X,
        realifiedCircularWeyl_majorana_square Y]

    _ = (majoranaSlash X + majoranaSlash Y) * (majoranaSlash X + majoranaSlash Y) -
          majoranaSlash X * majoranaSlash X - majoranaSlash Y * majoranaSlash Y := by
      rw [← hMajoranaAdd]
    _ = majoranaSlash X * majoranaSlash Y + majoranaSlash Y * majoranaSlash X :=
      (anticommutator_eq_square_sub _ _).symm

/- The realified circular Weyl connection and the real Majorana CAR slash
have the same polarized Minkowski Clifford relation on the doubled Krein
carrier. This identifies the actual circular operator anticommutator with
the spacetime metric, not just with a second abstract slash representation. -/
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem realifiedCircularWeyl_anticommutator_eq_minkowski
    (X Y : InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) *
        realifiedCircularMatrixEnd
          (circularConnectionMat4 (realMinkowskiCircularCoordinate Y)) +
      realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate Y)) *
        realifiedCircularMatrixEnd
          (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) =
      (2 * (X.t * Y.t - X.x * Y.x - X.y * Y.y - X.z * Y.z)) •
        (1 : Module.End ℝ KreinFrame4) := by
  have hPolar := realifiedCircularWeyl_majorana_polarization X Y
  change
    realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) *
        realifiedCircularMatrixEnd
          (circularConnectionMat4 (realMinkowskiCircularCoordinate Y)) +
      realifiedCircularMatrixEnd
        (circularConnectionMat4 (realMinkowskiCircularCoordinate Y)) *
        realifiedCircularMatrixEnd
          (circularConnectionMat4 (realMinkowskiCircularCoordinate X)) =
    realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana Y) +
      realThreeMatrixTensorOnH4 (realMinkowskiMajorana Y) *
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) at hPolar
  calc
    _ = realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) *
          realThreeMatrixTensorOnH4 (realMinkowskiMajorana Y) +
        realThreeMatrixTensorOnH4 (realMinkowskiMajorana Y) *
          realThreeMatrixTensorOnH4 (realMinkowskiMajorana X) := hPolar
    _ = _ := by
      have hCAR := congrArg realThreeMatrixTensorOnH4
        (realMinkowskiMajorana_anticommutator X Y)
      simpa only [map_mul, map_add, map_smul, map_one] using hCAR

/-- Realification preserves the chiral Peirce splitting of the circular
connection. This uses the source owner's off-block connection and transports
its projector identity to the actual doubled real carrier. -/
theorem realifiedCircularConnection_peirceDecomposition (x : Coordinate) :
    let P := realifiedCircularMatrixEnd chiralProjMat4
    let A := realifiedCircularMatrixEnd (circularConnectionMat4 x)
    P * A * (1 - P) + (1 - P) * A * P = A := by
  have hSource :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi chiralProjMat4
        (circularConnectionMat4 x) (circularConnectionMat4 x) =
          circularConnectionMat4 x := by
    simpa [chiralProjMat4, circularConnectionMat4] using
      genPhi_chiralOffBlock4 (weylUpperMat x) (weylLowerMat x)
  have hComplement :
      1 - realifiedCircularMatrixEnd chiralProjMat4 =
        realifiedCircularMatrixEnd (1 - chiralProjMat4) := by
    calc
      _ = realifiedCircularMatrixEnd 1 - realifiedCircularMatrixEnd chiralProjMat4 := by
        rw [realifiedCircularMatrixEnd_one]
      _ = realifiedCircularMatrixEnd (1 - chiralProjMat4) :=
        (realifiedCircularMatrixEnd_sub _ _).symm
  have hCornerPlus :
      realifiedCircularMatrixEnd chiralProjMat4 *
          realifiedCircularMatrixEnd (circularConnectionMat4 x) *
          (1 - realifiedCircularMatrixEnd chiralProjMat4) =
        realifiedCircularMatrixEnd
          (chiralProjMat4 * circularConnectionMat4 x * (1 - chiralProjMat4)) := by
    rw [hComplement, ← realifiedCircularMatrixEnd_mul, ← realifiedCircularMatrixEnd_mul]
  have hCornerMinus :
      (1 - realifiedCircularMatrixEnd chiralProjMat4) *
          realifiedCircularMatrixEnd (circularConnectionMat4 x) *
          realifiedCircularMatrixEnd chiralProjMat4 =
        realifiedCircularMatrixEnd
          ((1 - chiralProjMat4) * circularConnectionMat4 x * chiralProjMat4) := by
    rw [hComplement, ← realifiedCircularMatrixEnd_mul, ← realifiedCircularMatrixEnd_mul]
  change realifiedCircularMatrixEnd chiralProjMat4 *
      realifiedCircularMatrixEnd (circularConnectionMat4 x) *
        (1 - realifiedCircularMatrixEnd chiralProjMat4) +
    (1 - realifiedCircularMatrixEnd chiralProjMat4) *
      realifiedCircularMatrixEnd (circularConnectionMat4 x) *
        realifiedCircularMatrixEnd chiralProjMat4 =
      realifiedCircularMatrixEnd (circularConnectionMat4 x)
  rw [hCornerPlus, hCornerMinus]
  have h := congrArg realifiedCircularMatrixEnd hSource
  simpa [InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus] using h

/-- The existing three-mode real CAR equivalence transports the circular
connection square identity to its inverse image in the genuine Koszul tensor
algebra. No replacement multiplication or carrier is introduced. -/
theorem circularConnection_square_eq_curvatureInRealCAR (x : Coordinate) :
    realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd
      (circularConnectionMat4 x)) *
        realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd
          (circularConnectionMat4 x)) =
      realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd
        (circularCurvatureMat4 x)) := by
  apply realThreeMatrixTensorOnH4.injective
  simp only [realThreeMatrixTensorOnH4.apply_symm_apply]
  rw [map_mul, realThreeMatrixTensorOnH4.apply_symm_apply]
  exact (realifiedCircularCurvature_eq_connection_square x).symm

/-- In the existing real three-mode CAR algebra, the inverse images under its
owner equivalence preserve the source chiral Peirce decomposition. The source
projection remains distinct from CAR parity and Krein-frame chirality. -/
theorem realCAR_circularConnection_peirceDecomposition (x : Coordinate) :
    realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd chiralProjMat4) *
        realThreeMatrixTensorOnH4.symm
          (realifiedCircularMatrixEnd (circularConnectionMat4 x)) *
        (1 - realThreeMatrixTensorOnH4.symm
          (realifiedCircularMatrixEnd chiralProjMat4)) +
      (1 - realThreeMatrixTensorOnH4.symm
        (realifiedCircularMatrixEnd chiralProjMat4)) *
        realThreeMatrixTensorOnH4.symm
          (realifiedCircularMatrixEnd (circularConnectionMat4 x)) *
        realThreeMatrixTensorOnH4.symm (realifiedCircularMatrixEnd chiralProjMat4) =
      realThreeMatrixTensorOnH4.symm
        (realifiedCircularMatrixEnd (circularConnectionMat4 x)) := by
  apply realThreeMatrixTensorOnH4.injective
  simpa [map_mul, map_add, map_sub, map_one] using
      realifiedCircularConnection_peirceDecomposition x

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
    simp [InfoGeometry.Clifford.Cl11GradedTensorMorita.head,
      matrixE01, matrixE10,
      realPauliX, realPauliEpsilon, realPauliZ,
      AlgEquiv.coe_toAlgHom,
      InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge.blockRealify,
      Matrix.single,
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

/-! ### Rest-frame comparison with the real Peirce translation owner

At rest, the existing two-factor Peirce translation and its complementary
charge have the same anticommutator as the explicitly constructed three-mode
real CAR charge pair. The comparison is made after both owners' existing
algebra maps land on `KreinFrame4`; it does not identify the individual
charges or claim a general-momentum factorization.
-/

/-- The real `FourSpace` momentum at rest, normalized to the
super-Poincaré convention `{Q,Q†} = 2P₀`. -/
def realRestFrameMomentum (E : ℝ) : FourSpace := (2 * E) • unitTimeMomentum

/-- The soldered rest momentum matrix is `2E` times the real identity, in the
normalization `{Q,Q†} = 2P₀`. -/
theorem realMomentum_realRestFrame (E : ℝ) :
    realMomentum (realRestFrameMomentum E) = (2 * E) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  calc
    realMomentum (realRestFrameMomentum E) = (2 * E) • realMomentum unitTimeMomentum := by
      change fourSpaceEquivMat2Real ((2 * E) • unitTimeMomentum) =
        (2 * E) • fourSpaceEquivMat2Real unitTimeMomentum
      exact fourSpaceEquivMat2Real.map_smul (2 * E) unitTimeMomentum
    _ = (2 * E) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [realMomentum_unitTime]

/-- In the rest frame, the real Peirce translation pair and the constructed
real CAR supercharge pair have exactly the same operator anticommutator on the
doubled Krein carrier. This uses the existing Peirce translation theorem,
the existing real three-mode representation, and the CAR construction above.
-/
theorem realRestFrameCARCharges_match_PeirceTranslation
    (E : ℝ) (hE : 0 ≤ E) :
    let p := realRestFrameMomentum E
    realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode (translationInGradedTensor p)) *
        realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode conjugatePeirceCharge) +
      realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode conjugatePeirceCharge) *
        realThreeMatrixTensorOnH4
          (realTwoMatrixPairIntoThreeMode (translationInGradedTensor p)) =
      realRestFrameAnnihilationCharge E * realRestFrameCreationCharge E +
        realRestFrameCreationCharge E * realRestFrameAnnihilationCharge E := by
  dsimp
  rw [realKrein_gradedPair_translationCharge_anticommutator_eq_diagonalMomentum]
  rw [realRestFrameCARCharges_anticommutator E hE]
  have hdiag : diagonalMomentumOperator (realRestFrameMomentum E) =
      (2 * E) • (1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [diagonalMomentumOperator]
    rw [realMomentum_realRestFrame E]
    ext i j a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.smul_apply]
  rw [hdiag]
  simp [map_smul]

/-- At strictly positive rest energy, the Peirce translation and its lower
corner charge agree term by term with the CAR annihilation/creation pair,
after the explicit reciprocal normalization. The translation side carries
the factor `2E`; the CAR charges each carry `sqrt (2E)`. This strengthens
the anticommutator comparison above to an actual pair identification on the
same real doubled-Krein representation. -/
theorem realRestFramePeirceCharges_rescale_to_CAR
    (E : ℝ) (hE : 0 < E) :
    realThreeMatrixTensorOnH4
        (realTwoMatrixPairIntoThreeMode
          (translationInGradedTensor (realRestFrameMomentum E))) =
      Real.sqrt (2 * E) • realRestFrameAnnihilationCharge E ∧
    realThreeMatrixTensorOnH4
        (realTwoMatrixPairIntoThreeMode conjugatePeirceCharge) =
      (Real.sqrt (2 * E))⁻¹ • realRestFrameCreationCharge E := by
  have h2E : 0 < 2 * E := mul_pos (by norm_num) hE
  have hroot0 : Real.sqrt (2 * E) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 h2E)
  have hroot : Real.sqrt (2 * E) * Real.sqrt (2 * E) = 2 * E := by
    rw [← pow_two, Real.sq_sqrt (le_of_lt h2E)]
  constructor
  · have hTranslation :
        realTwoMatrixPairIntoThreeMode
            (translationInGradedTensor (realRestFrameMomentum E)) =
          (Real.sqrt (2 * E) * Real.sqrt (2 * E)) •
            realThreeAnnihilationHead := by
      rw [translationInGradedTensor_eq_odd_tmul,
        realTwoMatrixPairIntoThreeMode_tmul]
      have hmomentum : realMomentum (realRestFrameMomentum E) =
          (2 * E) • (1 : M2R) := realMomentum_realRestFrame E
      have hparity : matrixParity ((2 * E) • (1 : M2R)) =
          (2 * E) • (1 : M2R) := by
        rw [map_smul, map_one]
      rw [hmomentum, hparity]
      change (InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv.symm
          matrixE01) ᵍ⊗ₜ[ℝ]
          ((2 * E) • (1 : twoMatrixGradedTensor)) = _
      rw [show (InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv.symm
          matrixE01) ᵍ⊗ₜ[ℝ]
          ((2 * E) • (1 : twoMatrixGradedTensor)) =
            (2 * E) • ((InfoGeometry.Clifford.Cl11GradedMorita.cl11StandardEquiv.symm
              matrixE01) ᵍ⊗ₜ[ℝ]
              (1 : twoMatrixGradedTensor)) by
            dsimp [GradedTensorProduct.tmul]
            rw [TensorProduct.tmul_smul, map_smul]]
      change (2 * E) • realThreeAnnihilationHead = _
      rw [hroot]
    rw [hTranslation, map_smul]
    rw [realRestFrameAnnihilationCharge]
    rw [smul_smul]
  · have hCreation : conjugatePeirceCharge = creation₀ := by
      apply twoMatrixGradedTensorMoritaEquiv.injective
      rw [conjugatePeirceCharge, AlgEquiv.apply_symm_apply,
        creation₀, twoMatrixGradedTensorMoritaEquiv_tmul]
      ext i j a b
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        simp [conjugatePeirceChargeBlock, GradedTensorWeylBridge.matrixE10,
          matrixParity_apply, Matrix.single]
    rw [hCreation,
      InfoGeometry.Canonical.RealSolderingWeylKreinBridge.realTwoMatrixPairIntoThreeMode_creation₀,
      realRestFrameCreationCharge]
    rw [smul_smul, inv_mul_cancel₀ hroot0, one_smul]

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

/-- A circular time-Majorana generator cannot equal a Peirce translation
generator in the existing three-mode real Koszul algebra: the former squares
to one, while the latter squares to zero. Thus the unit-time anticommutator
identity above is genuinely a relation between pairs, not a generator
identification. -/
theorem circularMajoranaTime_ne_PeirceTranslation
    (i : Fin 3) (p : FourSpace) :
    circularMajoranaTime i ≠
      realTwoMatrixPairIntoThreeMode (translationInGradedTensor p) := by
  intro h
  have hsq := congrArg
    (fun A : realThreeMatrixGradedTensor => A * A) h
  have hMajoranaSq := (circularMajorana_splitClifford_relations i).1
  have hTranslationSq :
      realTwoMatrixPairIntoThreeMode (translationInGradedTensor p) *
          realTwoMatrixPairIntoThreeMode (translationInGradedTensor p) = 0 := by
    calc
      _ = realTwoMatrixPairIntoThreeMode
          (translationInGradedTensor p * translationInGradedTensor p) := by
            rw [map_mul]
      _ = 0 := by rw [translationInGradedTensor_square, map_zero]
  rw [hMajoranaSq, hTranslationSq] at hsq
  have hEnd :
      (1 : Module.End ℝ KreinFrame4) = 0 := by
    have h' := congrArg realThreeMatrixTensorOnH4 hsq
    rw [map_one, map_zero] at h'
    exact h'
  exact one_ne_zero hEnd

end InfoGeometry.Canonical.RealChiralCARTranslationSynthesis
