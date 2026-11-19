/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
import InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
import InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
import InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance

/-!
# Operatorial coordinates in the circular Peirce basis

This owner exposes the already-proved `Module.Basis` and axial-flow facts in
the natural eight coordinates.  Every statement is linear-operator algebra on
the full split-octonion carrier; no associativity of its multiplication is
used or asserted.
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates

open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
open InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

abbrev CanonicalZorn :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

theorem circularPeirceBasis_coordinate_expansion (X : CanonicalZorn) :
    X =
      coordinateEquiv X 0 • uPlus +
        coordinateEquiv X 1 • rootPlus 0 +
        coordinateEquiv X 2 • rootPlus 1 +
        coordinateEquiv X 3 • rootPlus 2 +
        coordinateEquiv X 4 • uMinus +
        coordinateEquiv X 5 • rootMinus 0 +
        coordinateEquiv X 6 • rootMinus 1 +
        coordinateEquiv X 7 • rootMinus 2 := by
  calc
    X = ∑ i : Fin 8,
        (circularPeirceBasis.equivFun X i) • circularPeirceBasis i :=
      (circularPeirceBasis_sum_repr X).symm
    _ = _ := by
      rw [Fin.sum_univ_eight]
      simp only [circularPeirceBasis_zero, circularPeirceBasis_one,
        circularPeirceBasis_two, circularPeirceBasis_three,
        circularPeirceBasis_four, circularPeirceBasis_five,
        circularPeirceBasis_six, circularPeirceBasis_seven]
      simp only [coordinateEquiv]

theorem axialFlow_coordinate_expansion (t : ℝ) (X : CanonicalZorn) :
    axialFlow t X =
      ∑ i : Fin 8,
        (Real.exp (t * axialWeight i) * coordinateEquiv X i) •
          circularPeirceBasis i := by
  calc
    axialFlow t X =
        ∑ i : Fin 8, coordinateEquiv (axialFlow t X) i •
          circularPeirceBasis i :=
      (circularPeirceBasis_sum_repr (axialFlow t X)).symm
    _ = ∑ i : Fin 8,
        (Real.exp (t * axialWeight i) * coordinateEquiv X i) •
          circularPeirceBasis i := by
      congr 1
      funext i
      rw [coordinateEquiv_axialFlow_apply]

theorem axialGrading_coordinate_expansion (X : CanonicalZorn) :
    axialGrading X =
      ∑ i : Fin 8,
        (axialWeight i * coordinateEquiv X i) •
          circularPeirceBasis i := by
  calc
    axialGrading X =
        ∑ i : Fin 8, coordinateEquiv (axialGrading X) i •
          circularPeirceBasis i :=
      (circularPeirceBasis_sum_repr (axialGrading X)).symm
    _ = ∑ i : Fin 8,
        (axialWeight i * coordinateEquiv X i) •
          circularPeirceBasis i := by
      congr 1
      funext i
      rw [coordinateEquiv_axialGrading_apply]

theorem ellCommutatorCoordinate_apply_diagonal (x : Coordinate) (i : Fin 8) :
    ellCommutatorCoordinate x i =
      (2 : ℝ) * axialWeight i * x i := by
  have hcomm : ellCommutator = (2 : ℝ) • axialGrading := by
    apply LinearMap.ext
    intro X
    simp [axialGrading]
  rw [ellCommutatorCoordinate_apply, hcomm]
  simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [coordinateEquiv_axialGrading_apply]
  simp only [coordinateEquiv.apply_symm_apply]
  ring

theorem leftCoordinateOperator_uPlus_apply (x : Coordinate) :
    leftCoordinateOperator uPlus x =
      fun i => if i.val < 4 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val < 4 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val < 4
        · simp only [Pi.add_apply, if_pos hi]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val < 4
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi, RingHom.id_apply]
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero,
            RingHom.id_apply] }
  have hT : leftCoordinateOperator uPlus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (uPlus * frame i) =
          if i.val < 4 then Pi.single i 1 else 0 := by
      rw [uPlus_mul_frame]
      fin_cases i
      · simpa [frame] using coordinateEquiv_apply_frame 0
      · simpa [frame] using coordinateEquiv_apply_frame 1
      · simpa [frame] using coordinateEquiv_apply_frame 2
      · simpa [frame] using coordinateEquiv_apply_frame 3
      · simp
      · simp
      · simp
      · simp
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [leftCoordinateOperator_on_frame]
    rw [hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

/-- Coordinate transport of the native left-regular operator. -/
theorem coordinateEquiv_leftRegular_apply (A X : CanonicalZorn) :
    coordinateEquiv (leftRegular A X) =
      leftCoordinateOperator A (coordinateEquiv X) := by
  change coordinateEquiv (A * X) =
    leftCoordinateOperator A (coordinateEquiv X)
  rw [← coordinateEquiv.symm_apply_apply X, ← leftCoordinateOperator_apply]
  simp

theorem rightCoordinateOperator_uMinus_apply (x : Coordinate) :
    rightCoordinateOperator uMinus x =
      fun i => if 0 < i.val ∧ i.val < 5 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if 0 < i.val ∧ i.val < 5 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : 0 < i.val ∧ i.val < 5
        · simp only [Pi.add_apply, if_pos hi, add_zero, zero_add]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : 0 < i.val ∧ i.val < 5
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi] <;> rfl
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero] <;> rfl }
  have hT : rightCoordinateOperator uMinus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (frame i * uMinus) =
          if 0 < i.val ∧ i.val < 5 then Pi.single i 1 else 0 := by
      rw [frame_mul_uMinus]
      fin_cases i
      · simp
      · simpa [frame] using coordinateEquiv_apply_frame 1
      · simpa [frame] using coordinateEquiv_apply_frame 2
      · simpa [frame] using coordinateEquiv_apply_frame 3
      · simpa [frame] using coordinateEquiv_apply_frame 4
      · simp
      · simp
      · simp
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [rightCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

theorem leftCoordinateOperator_uMinus_apply (x : Coordinate) :
    leftCoordinateOperator uMinus x =
      fun i => if i.val ≥ 4 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val ≥ 4 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val ≥ 4
        · simp only [Pi.add_apply, if_pos hi, add_zero, zero_add]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val ≥ 4
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi] <;> rfl
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero] <;> rfl }
  have hT : leftCoordinateOperator uMinus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (uMinus * frame i) =
          if i.val ≥ 4 then Pi.single i 1 else 0 := by
      rw [uMinus_mul_frame]
      fin_cases i
      · simp
      · simp
      · simp
      · simp
      · simpa [frame] using coordinateEquiv_apply_frame 4
      · simpa [frame] using coordinateEquiv_apply_frame 5
      · simpa [frame] using coordinateEquiv_apply_frame 6
      · simpa [frame] using coordinateEquiv_apply_frame 7
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [leftCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

/-- The regular Tetraktys element `J = L_{u₊} - L_{u₋}` is diagonal in the
actual Ell-circular basis: its positive sector is spanned by frame indices
`0..3` and its negative sector by `4..7`. This transports the endomorphism
algebra generator to the coordinate carrier explicitly. -/
theorem regularJ_uPlus_uMinus_coordinate_apply (x : Coordinate) :
    coordinateEquiv
        (regularJ uPlus uMinus (coordinateEquiv.symm x)) =
      fun i => if i.val < 4 then x i else -x i := by
  change coordinateEquiv
      ((leftRegular uPlus - leftRegular uMinus) (coordinateEquiv.symm x)) = _
  rw [LinearMap.sub_apply, map_sub,
    coordinateEquiv_leftRegular_apply, coordinateEquiv_leftRegular_apply]
  rw [leftCoordinateOperator_uPlus_apply, leftCoordinateOperator_uMinus_apply]
  funext i
  by_cases hi : i.val < 4
  · simp [hi, Nat.not_le.mpr hi]
  · have hi' : i.val ≥ 4 := Nat.le_of_not_gt hi
    simp [hi, hi']

/-- The regular `J` generator squares to the identity on the full carrier. -/
theorem regularJ_uPlus_uMinus_sq :
    regularJ uPlus uMinus * regularJ uPlus uMinus = 1 := by
  apply LinearMap.ext
  intro X
  simp only [Module.End.mul_apply, Module.End.one_apply]
  apply coordinateEquiv.injective
  let x := coordinateEquiv X
  have h₁ := regularJ_uPlus_uMinus_coordinate_apply x
  have h₂ := regularJ_uPlus_uMinus_coordinate_apply
    (coordinateEquiv (regularJ uPlus uMinus (coordinateEquiv.symm x)))
  rw [coordinateEquiv.symm_apply_apply, h₁] at h₂
  funext i
  by_cases hi : i.val < 4
  · have h₂i := congrFun h₂ i
    simp [hi] at h₂i
    simpa [x, hi] using h₂i
  · have hi' : i.val ≥ 4 := Nat.le_of_not_gt hi
    have h₂i := congrFun h₂ i
    simp [hi, hi'] at h₂i
    simpa [x, hi, hi'] using h₂i

/-- In this distinguished Peirce pair, the `Φ` regular generator is the
identity on the carrier. -/
theorem regularPhi_uPlus_uMinus_eq_one :
    regularPhi uPlus uMinus = 1 := by
  apply LinearMap.ext
  intro X
  change uPlus * X + uMinus * X = X
  rw [← InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    uPlus_add_uMinus]
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul X

/-- The two disjoint coordinate Peirce projections have zero compositions;
this proves the corresponding `V` and `Σ` regular generators vanish. -/
theorem regularLeftProjection_compositions_zero :
    leftRegular uPlus * leftRegular uMinus = 0 ∧
      leftRegular uMinus * leftRegular uPlus = 0 := by
  constructor
  · apply LinearMap.ext
    intro X
    apply coordinateEquiv.injective
    change coordinateEquiv
      (leftRegular uPlus (leftRegular uMinus X)) = coordinateEquiv 0
    rw [coordinateEquiv_leftRegular_apply, coordinateEquiv_leftRegular_apply,
      leftCoordinateOperator_uMinus_apply, leftCoordinateOperator_uPlus_apply]
    rw [map_zero]
    funext i
    by_cases hi : i.val < 4
    · simp [hi, Nat.not_le.mpr hi]
    · have hi' : i.val ≥ 4 := Nat.le_of_not_gt hi
      simp [hi, hi']
  · apply LinearMap.ext
    intro X
    apply coordinateEquiv.injective
    change coordinateEquiv
      (leftRegular uMinus (leftRegular uPlus X)) = coordinateEquiv 0
    rw [coordinateEquiv_leftRegular_apply, coordinateEquiv_leftRegular_apply,
      leftCoordinateOperator_uPlus_apply, leftCoordinateOperator_uMinus_apply]
    rw [map_zero]
    funext i
    by_cases hi : i.val < 4
    · simp [hi, Nat.not_le.mpr hi]
    · have hi' : i.val ≥ 4 := Nat.le_of_not_gt hi
      simp [hi, hi']

/-- The anticommutator channel `V` and commutator channel `Σ` both vanish
for the complementary `u₊/u₋` idempotents in the Ell-circular convention. -/
theorem regularV_regularSig_uPlus_uMinus_eq_zero :
    regularV uPlus uMinus = 0 ∧ regularSig uPlus uMinus = 0 := by
  rcases regularLeftProjection_compositions_zero with ⟨hpm, hmp⟩
  exact ⟨by simp [regularV, hpm, hmp], by simp [regularSig, hpm, hmp]⟩

/-- Conjugate a regular endomorphism onto the actual Ell-circular
coordinate carrier. -/
def ellCoordinateConjugate
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    Module.End ℝ Coordinate :=
  coordinateEquiv.conjAlgEquiv ℝ T

/-- Commutator superoperators on Ell-coordinate endomorphisms. -/
def ellCoordinateComm (A B : Module.End ℝ Coordinate) :
    Module.End ℝ Coordinate := A * B - B * A

/-- Double-commutator superoperators on Ell-coordinate endomorphisms. -/
def ellCoordinateDoubleComm (A B : Module.End ℝ Coordinate) :
    Module.End ℝ Coordinate := ellCoordinateComm A (ellCoordinateComm A B)

/-- Conjugation by the circular-coordinate equivalence preserves the
regular Tetraktys double commutator. -/
theorem ellCoordinateConjugate_doubleComm
    (H T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    ellCoordinateConjugate (doubleComm H T) =
      ellCoordinateDoubleComm (ellCoordinateConjugate H) (ellCoordinateConjugate T) := by
  change (coordinateEquiv.conjAlgEquiv ℝ) (doubleComm H T) = _
  simp only [doubleComm, operatorComm, map_sub, map_mul]
  rfl

/-- For the complementary Ell-circular projectors, the `Φ`, `V`, and `Σ`
regular channels have zero induced double commutator. -/
theorem ellCircular_regularTetraktys_doubleComm_reduction (T :
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    ellCoordinateDoubleComm (ellCoordinateConjugate (regularPhi uPlus uMinus))
      (ellCoordinateConjugate T) = 0 ∧
    ellCoordinateDoubleComm (ellCoordinateConjugate (regularV uPlus uMinus))
      (ellCoordinateConjugate T) = 0 ∧
    ellCoordinateDoubleComm (ellCoordinateConjugate (regularSig uPlus uMinus))
      (ellCoordinateConjugate T) = 0 := by
  have hΦ : regularPhi uPlus uMinus = 1 := regularPhi_uPlus_uMinus_eq_one
  have hVS := regularV_regularSig_uPlus_uMinus_eq_zero
  constructor
  · rw [← ellCoordinateConjugate_doubleComm, hΦ]
    simp [doubleComm, operatorComm, ellCoordinateConjugate]
  · constructor
    · rw [← ellCoordinateConjugate_doubleComm, hVS.1]
      simp [doubleComm, operatorComm, ellCoordinateConjugate]
    · rw [← ellCoordinateConjugate_doubleComm, hVS.2]
      simp [doubleComm, operatorComm, ellCoordinateConjugate]

/-- On the Ell coordinate carrier, regular `J` acts by `+1` on indices
`0..3` and `-1` on indices `4..7`. -/
theorem ellCircular_regularJ_apply (x : Coordinate) :
    ellCoordinateConjugate (regularJ uPlus uMinus) x =
      fun i => if i.val < 4 then x i else -x i := by
  simpa [ellCoordinateConjugate, LinearEquiv.conjAlgEquiv_apply] using
    regularJ_uPlus_uMinus_coordinate_apply x

/-- The double commutator by regular `J` annihilates same-sector matrix
units and multiplies cross-sector matrix units by four. -/
theorem ellCircular_regularJ_doubleComm_matrixUnit (T : Module.End ℝ Coordinate)
    (i j : Fin 8) :
    ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) T
        (Pi.single j (1 : ℝ)) i =
      if (i.val < 4) = (j.val < 4) then 0 else
        4 * T (Pi.single j (1 : ℝ)) i := by
  let H := ellCoordinateConjugate (regularJ uPlus uMinus)
  have hHapply (x : Coordinate) (k : Fin 8) :
      H x k = (if k.val < 4 then (1 : ℝ) else -1) * x k := by
    have h := congrFun (ellCircular_regularJ_apply x) k
    simpa [H, smul_eq_mul] using h
  have hHe : H (Pi.single j (1 : ℝ)) =
      (if j.val < 4 then (1 : ℝ) else -1) • Pi.single j 1 := by
    ext k
    simp only [Pi.smul_apply]
    rw [hHapply]
    by_cases hj : j.val < 4 <;> by_cases hk : k = j <;>
      simp [hj, hk, smul_eq_mul]
  have hHsq : H * H = 1 := by
    simpa [H, ellCoordinateConjugate] using
      congrArg (coordinateEquiv.conjAlgEquiv ℝ)
        regularJ_uPlus_uMinus_sq
  have hdouble : ellCoordinateDoubleComm H T =
      2 • (T - H * T * H) := by
    have hHsq_apply : ∀ x : Coordinate, H (H x) = x := by
      intro x
      have h := congrArg (fun F : Module.End ℝ Coordinate => F x) hHsq
      simpa only [Module.End.mul_apply, Module.End.one_apply] using h
    unfold ellCoordinateDoubleComm ellCoordinateComm
    apply LinearMap.ext
    intro x
    change H (H (T x) - T (H x)) -
        (H (T (H x)) - T (H (H x))) =
      2 • (T x - H (T (H x)))
    rw [map_sub, hHsq_apply (T x), hHsq_apply x, two_smul]
    ring
  rw [show ellCoordinateConjugate (regularJ uPlus uMinus) = H from rfl,
    hdouble]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4 <;>
    simp [Module.End.mul_apply, hHe, hHapply, hi, hj] <;> ring

theorem rightCoordinateOperator_uPlus_apply (x : Coordinate) :
    rightCoordinateOperator uPlus x =
      fun i => if i.val = 0 ∨ i.val ≥ 5 then x i else 0 := by
  let T : Coordinate →ₗ[ℝ] Coordinate :=
    { toFun := fun y i => if i.val = 0 ∨ i.val ≥ 5 then y i else 0
      map_add' := by
        intro y z
        funext i
        by_cases hi : i.val = 0 ∨ i.val ≥ 5
        · simp only [Pi.add_apply, if_pos hi, add_zero, zero_add]
        · simp only [Pi.add_apply, if_neg hi, zero_add]
      map_smul' := by
        intro c y
        funext i
        by_cases hi : i.val = 0 ∨ i.val ≥ 5
        · simp only [Pi.smul_apply, smul_eq_mul, if_pos hi] <;> rfl
        · simp only [Pi.smul_apply, smul_eq_mul, if_neg hi, mul_zero] <;> rfl }
  have hT : rightCoordinateOperator uPlus = T := by
    have hcoord (i : Fin 8) :
        coordinateEquiv (frame i * uPlus) =
          if i.val = 0 ∨ i.val ≥ 5 then Pi.single i 1 else 0 := by
      rw [frame_mul_uPlus]
      fin_cases i
      · simpa [frame] using coordinateEquiv_apply_frame 0
      · simp
      · simp
      · simp
      · simp
      · simpa [frame] using coordinateEquiv_apply_frame 5
      · simpa [frame] using coordinateEquiv_apply_frame 6
      · simpa [frame] using coordinateEquiv_apply_frame 7
    apply (Pi.basisFun ℝ (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rw [rightCoordinateOperator_on_frame, hcoord]
    funext j
    fin_cases i <;> fin_cases j <;> simp [T]
  exact congrArg (fun f : Coordinate →ₗ[ℝ] Coordinate => f x) hT

/-- The native Zorn multiplication is represented in the circular coordinates
by the bilinear basis-product kernel.  This is a coordinate expansion only;
it does not reassociate any triple product and does not assert associativity. -/
theorem coordinateEquiv_mul_basis_kernel (X Y : CanonicalZorn) :
    coordinateEquiv (X * Y) =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (coordinateEquiv X i * coordinateEquiv Y j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
  have hX := circularPeirceBasis_sum_repr X
  have hY := circularPeirceBasis_sum_repr Y
  have hX' : ∑ i : Fin 8, coordinateEquiv X i • circularPeirceBasis i = X := by
    simpa [coordinateEquiv] using hX
  have hY' : ∑ i : Fin 8, coordinateEquiv Y i • circularPeirceBasis i = Y := by
    simpa [coordinateEquiv] using hY
  calc
    coordinateEquiv (X * Y) = coordinateEquiv
        ((∑ i : Fin 8, (coordinateEquiv X i) • circularPeirceBasis i) *
          (∑ j : Fin 8, (coordinateEquiv Y j) • circularPeirceBasis j)) := by
      exact congrArg coordinateEquiv
        (congrArg₂ (fun A B : CanonicalZorn => A * B) hX'.symm hY'.symm)
    _ = ∑ i : Fin 8, ∑ j : Fin 8,
        (coordinateEquiv X i * coordinateEquiv Y j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
      have hprod :
          (∑ i : Fin 8, coordinateEquiv X i • circularPeirceBasis i) *
              (∑ j : Fin 8, coordinateEquiv Y j • circularPeirceBasis j) =
              ∑ i : Fin 8, ∑ j : Fin 8,
              (coordinateEquiv X i * coordinateEquiv Y j) •
                (circularPeirceBasis i * circularPeirceBasis j) := by
        change rightMultiplication
          (∑ j : Fin 8, coordinateEquiv Y j • circularPeirceBasis j)
          (∑ i : Fin 8, coordinateEquiv X i • circularPeirceBasis i) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [rightMultiplication_apply]
        change (coordinateEquiv X i • circularPeirceBasis i) *
          (∑ j : Fin 8, coordinateEquiv Y j • circularPeirceBasis j) = _
        rw [← leftMultiplication_apply, map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
          (coordinateEquiv X i • circularPeirceBasis i)
          (coordinateEquiv Y j • circularPeirceBasis j) = _
        rw [zMul_smul_right, zMul_smul_left, smul_smul]
        change _ = (coordinateEquiv X i * coordinateEquiv Y j) •
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
            (circularPeirceBasis i) (circularPeirceBasis j)
        rw [mul_comm]
      rw [hprod, map_sum coordinateEquiv]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_sum coordinateEquiv]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]

theorem leftCoordinateOperator_basis_kernel
    (A : CanonicalZorn) (x : Coordinate) :
    leftCoordinateOperator A x =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (coordinateEquiv A i * x j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
  rw [leftCoordinateOperator_apply]
  rw [coordinateEquiv_mul_basis_kernel]
  simp only [coordinateEquiv.apply_symm_apply]

theorem rightCoordinateOperator_basis_kernel
    (A : CanonicalZorn) (x : Coordinate) :
    rightCoordinateOperator A x =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (x i * coordinateEquiv A j) •
          coordinateEquiv (circularPeirceBasis i * circularPeirceBasis j) := by
  rw [rightCoordinateOperator_apply]
  rw [coordinateEquiv_mul_basis_kernel]
  simp only [coordinateEquiv.apply_symm_apply]

noncomputable def leftCoordinateOperatorMatrix (A : CanonicalZorn) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (leftCoordinateOperator A)

theorem leftCoordinateOperatorMatrix_apply (A : CanonicalZorn)
    (i j : Fin 8) :
    leftCoordinateOperatorMatrix A i j =
      ∑ k : Fin 8, coordinateEquiv A k *
        coordinateEquiv (circularPeirceBasis k * circularPeirceBasis j) i := by
  rw [leftCoordinateOperatorMatrix, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]
  rw [leftCoordinateOperator_on_frame]
  rw [coordinateEquiv_mul_basis_kernel]
  rw [Finset.sum_apply]
  classical
  simp only [circularPeirceBasis_apply]
  simp_rw [coordinateEquiv_apply_frame]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single j]
  · simp [Pi.single_apply, smul_eq_mul]
  · intro c hc hcj
    simp [hcj]
  · simp

noncomputable def rightCoordinateOperatorMatrix (A : CanonicalZorn) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (rightCoordinateOperator A)

theorem rightCoordinateOperatorMatrix_apply (A : CanonicalZorn)
    (i j : Fin 8) :
    rightCoordinateOperatorMatrix A i j =
      ∑ k : Fin 8, coordinateEquiv A k *
        coordinateEquiv (circularPeirceBasis j * circularPeirceBasis k) i := by
  rw [rightCoordinateOperatorMatrix, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]
  rw [rightCoordinateOperator_on_frame]
  rw [coordinateEquiv_mul_basis_kernel]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [coordinateEquiv_apply_frame, Pi.single_apply]
  · intro x hx hxj
    simp [hxj]
  · simp

noncomputable def ellCommutatorCoordinateMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    ellCommutatorCoordinate

theorem ellCommutatorCoordinateMatrix_eq_diagonal :
    ellCommutatorCoordinateMatrix =
      Matrix.diagonal (fun i => (2 : ℝ) * axialWeight i) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    ext i
    rw [ellCommutatorCoordinate_apply_diagonal]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, Matrix.diagonal,
      Matrix.one_apply]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

theorem ellCommutatorCoordinateMatrix_eq_two_axialGradingMatrix :
    ellCommutatorCoordinateMatrix = (2 : ℝ) • axialGradingMatrix := by
  rw [ellCommutatorCoordinateMatrix_eq_diagonal, axialGradingMatrix_eq_diagonal]
  ext i j
  simp [Matrix.diagonal]

noncomputable def leftCoordinateOperatorUPlusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (leftCoordinateOperator uPlus)

theorem leftCoordinateOperatorUPlusMatrix_eq_diagonal :
    leftCoordinateOperatorUPlusMatrix =
      Matrix.diagonal (fun i => if i.val < 4 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [leftCoordinateOperator_uPlus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

noncomputable def rightCoordinateOperatorUMinusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (rightCoordinateOperator uMinus)

theorem rightCoordinateOperatorUMinusMatrix_eq_diagonal :
    rightCoordinateOperatorUMinusMatrix =
      Matrix.diagonal (fun i => if 0 < i.val ∧ i.val < 5 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [rightCoordinateOperator_uMinus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

noncomputable def leftCoordinateOperatorUMinusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (leftCoordinateOperator uMinus)

theorem leftCoordinateOperatorUMinusMatrix_eq_diagonal :
    leftCoordinateOperatorUMinusMatrix =
      Matrix.diagonal (fun i => if i.val ≥ 4 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [leftCoordinateOperator_uMinus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

noncomputable def rightCoordinateOperatorUPlusMatrix :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (rightCoordinateOperator uPlus)

theorem rightCoordinateOperatorUPlusMatrix_eq_diagonal :
    rightCoordinateOperatorUPlusMatrix =
      Matrix.diagonal (fun i => if i.val = 0 ∨ i.val ≥ 5 then 1 else 0) := by
  exact coordinateOperatorMatrix_eq_diagonal _ _ (by
    intro j
    rw [rightCoordinateOperator_uPlus_apply]
    ext i
    simp [Pi.single_apply, Matrix.diagonal]
    by_cases h : i = j
    · subst i
      simp
    · simp [h])

theorem rightCoordinateOperatorUPlusMatrix_add_rightCoordinateOperatorUMinusMatrix :
    rightCoordinateOperatorUPlusMatrix + rightCoordinateOperatorUMinusMatrix =
      (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [rightCoordinateOperatorUPlusMatrix_eq_diagonal,
    rightCoordinateOperatorUMinusMatrix_eq_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    fin_cases i <;> simp [Matrix.diagonal, Matrix.one_apply]
  · simp [Matrix.diagonal, Matrix.one_apply, h]

theorem leftCoordinateOperatorUPlusMatrix_add_leftCoordinateOperatorUMinusMatrix :
    leftCoordinateOperatorUPlusMatrix + leftCoordinateOperatorUMinusMatrix =
      (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [leftCoordinateOperatorUPlusMatrix_eq_diagonal,
    leftCoordinateOperatorUMinusMatrix_eq_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i.val < 4
    · have hge : ¬ 4 ≤ i.val := by omega
      simp [Matrix.diagonal, Matrix.one_apply, hi, hge]
    · have hge : 4 ≤ i.val := by omega
      simp [Matrix.diagonal, Matrix.one_apply, hi, hge]
  · simp [Matrix.diagonal, Matrix.one_apply, h]

theorem axialFlow_mem_axialEigenspace (t w : ℝ) (X : CanonicalZorn)
    (hX : X ∈ axialEigenspace w) :
    axialFlow t X ∈ axialEigenspace w := by
  rw [mem_axialEigenspace_iff] at hX ⊢
  have hcomm := congrArg (fun T : Module.End ℝ CanonicalZorn => T X)
    (axialGrading_mul_axialFlow t)
  have hcomm' : axialGrading (axialFlow t X) =
      axialFlow t (axialGrading X) := by
    simpa only [Module.End.mul_apply] using hcomm
  change axialGrading (axialFlow t X) = w • axialFlow t X
  rw [hcomm']
  rw [hX, map_smul]

end InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates

namespace InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinatesWitnesses

theorem leftCoordinate_mat8_noncomm :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 8) (Fin 8) ℝ :=
    Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 8) (Fin 8) ℝ :=
    Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 8)) (0 : Fin 8)
  have hAB : (A * B) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 8)]
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

end InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinatesWitnesses
