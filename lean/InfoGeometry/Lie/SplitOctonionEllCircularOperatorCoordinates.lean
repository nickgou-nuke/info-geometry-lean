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
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
open InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

abbrev CanonicalZorn :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn

/-- Soldering map from Ell-circular coordinates to the quaternionic Cartesian
coordinates on the same canonical Zorn carrier.  It is the actual composition
of the Ell basis equivalence with the inverse Cartesian-to-Zorn equivalence. -/
def ellCircularToCartesianCoordinates :
    (Fin 8 → ℝ) ≃ₗ[ℝ]
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv.symm.trans
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm

/-- Each column of the soldering map is the Cartesian coordinate readout of
the corresponding actual Ell Peirce basis element. -/
theorem ellCircularToCartesianCoordinates_basis (j : Fin 8) :
    ellCircularToCartesianCoordinates (Pi.single j (1 : ℝ)) =
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame j) := by
  simp [ellCircularToCartesianCoordinates,
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_symm_single]

/-- The Ell-circular positive roots are not the Cartesian circular roots
under the identity map of the canonical Zorn carrier.  In the former basis,
the `y` coordinate is nonzero; the Cartesian image has `y = 0`.  Thus a
Cartesian root multiplication table cannot be applied to Ell roots without
first transporting the basis. -/
theorem ellRootPlus_ne_cartesianRootPlus (i : Fin 3) :
    InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i ≠
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
        (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i) := by
  intro h
  have hcoord := congrArg (fun z : CanonicalZorn => z.y i) h
  fin_cases i <;>
    norm_num [InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.chiralNull,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.quaternionAxis,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.ellAxis,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.axis,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.ellBasis,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.jUnit,
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] at hcoord

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

/-- Coordinate transport of the native left-regular operator. -/
theorem coordinateEquiv_leftRegular_apply (A X : CanonicalZorn) :
    coordinateEquiv (leftRegular A X) =
      leftCoordinateOperator A (coordinateEquiv X) := by
  change coordinateEquiv (A * X) =
    leftCoordinateOperator A (coordinateEquiv X)
  rw [← coordinateEquiv.symm_apply_apply X, ← leftCoordinateOperator_apply]
  simp

/-- The soldering map intertwines the left-regular action on the Ell basis
with the same native Zorn multiplication read in Cartesian coordinates.
This is the multiplication-compatible bridge between the two coordinate
carriers; the basis change is not being treated as an identification of their
coordinate vectors. -/
theorem ellCircularToCartesian_intertwines_leftRegular
    (A : CanonicalZorn) (x : Coordinate) :
    ellCircularToCartesianCoordinates (leftCoordinateOperator A x) =
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm
        (A * InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
          (ellCircularToCartesianCoordinates x)) := by
  have h : coordinateEquiv.symm (leftCoordinateOperator A x) =
      leftRegular A (coordinateEquiv.symm x) := by
    simpa using congrArg coordinateEquiv.symm
      (coordinateEquiv_leftRegular_apply A (coordinateEquiv.symm x)).symm
  have hs : InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
      (ellCircularToCartesianCoordinates x) = coordinateEquiv.symm x := by
    change InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv
      (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm
        (coordinateEquiv.symm x)) = coordinateEquiv.symm x
    exact InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.apply_symm_apply _
  change InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm
      (coordinateEquiv.symm (leftCoordinateOperator A x)) = _
  rw [h, leftRegular_apply]
  apply congrArg
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm
  rw [hs]

/-- Transport an endomorphism of Ell-circular coordinates to the Cartesian
coordinate carrier by the soldering equivalence.  This is conjugation of
linear operators; it does not identify the two coordinate bases. -/
def cartesianOperatorConjugate (T : Module.End ℝ Coordinate) :
    Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates :=
  ellCircularToCartesianCoordinates.conjAlgEquiv ℝ T

/-- Cartesian-coordinate basis obtained by transporting the standard Ell
coordinate basis along the actual soldering equivalence. -/
noncomputable def ellSolderedCartesianBasis :
    Module.Basis (Fin 8) ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates :=
  (Pi.basisFun ℝ (Fin 8)).map ellCircularToCartesianCoordinates

/-- Native quaternion-pair readout of each soldered frame vector.  The two
quaternions are recovered from the actual Zorn `a,b,x,y` fields by the inverse
of `cartesianZornLinearEquiv`; this records the coordinate formula without
identifying the Ell frame with the distinct quaternion-circular frame. -/
theorem ellSolderedCartesianBasis_coordinate_formula (i : Fin 8) :
    ellSolderedCartesianBasis i =
      ((((frame i).a + (frame i).b) / 2, ((frame i).x - (frame i).y) / 2),
       (((frame i).a - (frame i).b) / 2, ((frame i).x + (frame i).y) / 2)) := by
  simp [ellSolderedCartesianBasis, ellCircularToCartesianCoordinates,
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.coordinateEquiv_symm_single,
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv_symm_apply]

/-- The eight actual Ell-frame vectors after soldering, expressed in the
native pair of quaternion coordinates `(scalar, imaginary vector)`. -/
def ellSolderedCartesianFrame : Fin 8 →
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates
  | 0 => Prod.mk (Prod.mk (1 / 2 : ℝ) (0 : Fin 3 → ℝ))
      (Prod.mk (0 : ℝ) ((1 / 2 : ℝ) • (![1, 0, 0] : Fin 3 → ℝ)))
  | 1 => Prod.mk (Prod.mk (0 : ℝ) ((1 / 2 : ℝ) • (![1, 0, 0] : Fin 3 → ℝ)))
      (Prod.mk (-1 / 2 : ℝ) (0 : Fin 3 → ℝ))
  | 2 => Prod.mk (Prod.mk (0 : ℝ) ((1 / 2 : ℝ) • (![0, 1, 0] : Fin 3 → ℝ)))
      (Prod.mk (0 : ℝ) ((1 / 2 : ℝ) • (![0, 0, 1] : Fin 3 → ℝ)))
  | 3 => Prod.mk (Prod.mk (0 : ℝ) ((1 / 2 : ℝ) • (![0, 0, 1] : Fin 3 → ℝ)))
      (Prod.mk (0 : ℝ) ((-1 / 2 : ℝ) • (![0, 1, 0] : Fin 3 → ℝ)))
  | 4 => Prod.mk (Prod.mk (1 / 2 : ℝ) (0 : Fin 3 → ℝ))
      (Prod.mk (0 : ℝ) ((-1 / 2 : ℝ) • (![1, 0, 0] : Fin 3 → ℝ)))
  | 5 => Prod.mk (Prod.mk (0 : ℝ) ((-1 / 2 : ℝ) • (![1, 0, 0] : Fin 3 → ℝ)))
      (Prod.mk (-1 / 2 : ℝ) (0 : Fin 3 → ℝ))
  | 6 => Prod.mk (Prod.mk (0 : ℝ) ((-1 / 2 : ℝ) • (![0, 1, 0] : Fin 3 → ℝ)))
      (Prod.mk (0 : ℝ) ((1 / 2 : ℝ) • (![0, 0, 1] : Fin 3 → ℝ)))
  | 7 => Prod.mk (Prod.mk (0 : ℝ) ((-1 / 2 : ℝ) • (![0, 0, 1] : Fin 3 → ℝ)))
      (Prod.mk (0 : ℝ) ((-1 / 2 : ℝ) • (![0, 1, 0] : Fin 3 → ℝ)))
  | _ => 0

/-- Exact coordinate table for the transported Ell-circular Peirce basis.
The proof expands the actual root definitions and canonical Zorn product. -/
theorem ellSolderedCartesianBasis_explicit (i : Fin 8) :
    ellSolderedCartesianBasis i = ellSolderedCartesianFrame i := by
  fin_cases i <;>
    rw [ellSolderedCartesianBasis_coordinate_formula] <;>
    norm_num [ellSolderedCartesianFrame, frame, uPlus, uMinus, rootPlus,
      rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit, jUnit,
      kQuaternionUnit, lUnit, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] <;>
    constructor <;> (funext j; fin_cases j <;> norm_num)

/-- The regular tetraktys generator `J = L_{u₊} - L_{u₋} = L_ℓ`, transported
from Ell coordinates to the quaternion-pair carrier. -/
noncomputable def cartesianRegularJ : Module.End ℝ
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates :=
  cartesianOperatorConjugate (leftCoordinateOperator lUnit)

/-- Exact quaternion-pair action of the regular `J` operator.  It mixes scalar
and vector coordinates; in particular it is not the distinct Cartesian
grading operator that kills both scalar coordinates. -/
theorem cartesianRegularJ_apply
    (q : InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates) :
    cartesianRegularJ q =
      Prod.mk
        (Prod.mk (q.2.2 0) (fun i : Fin 3 =>
          if i = 0 then -q.2.1 else if i = 1 then q.2.2 2 else -q.2.2 1))
        (Prod.mk (-q.1.2 0) (fun i : Fin 3 =>
          if i = 0 then q.1.1 else if i = 1 then -q.1.2 2 else q.1.2 1)) := by
  change ellCircularToCartesianCoordinates
    (leftCoordinateOperator lUnit (ellCircularToCartesianCoordinates.symm q)) = _
  rw [ellCircularToCartesian_intertwines_leftRegular]
  apply InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.injective
  rw [InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.apply_symm_apply]
  rcases q with ⟨⟨q₀, qᵥ⟩, ⟨r₀, rᵥ⟩⟩
  simp [InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv,
    InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    InfoGeometry.Canonical.ZornMatrix.mul]
  constructor
  · ring
  constructor
  · ring
  constructor
  · funext i
    fin_cases i <;> simp <;> ring
  · funext i
    fin_cases i <;> simp <;> ring

/-- The regular Peirce `J` action is not the normalized Cartesian
quaternion-triple grading: on the first quaternion's scalar unit, `J` produces
the second quaternion's first vector unit, while `cartesianEllGrading` kills
that scalar input. -/
theorem cartesianRegularJ_ne_cartesianEllGrading :
    cartesianRegularJ ≠
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianEllGrading := by
  intro h
  let oneCoord :
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates :=
    Prod.mk (Prod.mk (1 : ℝ) (0 : Fin 3 → ℝ)) (Prod.mk (0 : ℝ) (0 : Fin 3 → ℝ))
  have h₁ := congrArg (fun T : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates => T oneCoord) h
  rw [cartesianRegularJ_apply,
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianEllGrading_apply] at h₁
  have hentry := congrArg (fun z :
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates => z.2.2 0) h₁
  norm_num [oneCoord] at hentry

/-- Matrix coefficients of an operator are unchanged when both the operator
and its basis are transported through the Ell-to-Cartesian soldering map. -/
theorem ellSolderedCartesian_operatorMatrix_entry
    (T : Module.End ℝ Coordinate) (i j : Fin 8) :
    LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
        (cartesianOperatorConjugate T) i j =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) T i j := by
  simp [ellSolderedCartesianBasis, cartesianOperatorConjugate,
    LinearMap.toMatrix_apply, Module.Basis.map_repr]

/-- The regular Tetraktys element `J = L_{u₊} - L_{u₋}` is diagonal in the
actual Ell-circular basis: its positive sector is spanned by frame indices
`0..3` and its negative sector by `4..7`.  This transports the endomorphism
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

/-- The regular `J` generator squares to the identity on the full
split-octonion carrier, as witnessed in the Ell-circular coordinates. -/
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

/-- On the original split-octonion carrier's endomorphism algebra, the
double-commutator generated by the actual regular Peirce involution is a
scaled projection: `D² = 4D`. This is the carrier-level form of the sector
readout proved later in Ell coordinates. -/
theorem regularJ_uPlus_uMinus_doubleComm_square
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm
        (regularJ uPlus uMinus)
        (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm
          (regularJ uPlus uMinus) T) =
      4 • InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm
        (regularJ uPlus uMinus) T := by
  let H := regularJ uPlus uMinus
  have hH : H * H = 1 := regularJ_uPlus_uMinus_sq
  have hanti : H *
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T =
      -(InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T * H) := by
    have hleft : H * (H * T * H) = T * H := by
      calc
        H * (H * T * H) = (H * H) * T * H := by noncomm_ring
        _ = T * H := by rw [hH, one_mul]
    have hright : (H * T * H) * H = H * T := by
      calc
        (H * T * H) * H = H * T * (H * H) := by noncomm_ring
        _ = H * T := by rw [hH, mul_one]
    rw [InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm_eq_two_smul_sub_conjugate H T hH]
    simp only [two_smul, mul_add, add_mul, mul_sub, sub_mul]
    rw [hleft, hright]
    noncomm_ring
  exact InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm_eq_four_smul_of_anticommutes
    H (InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H T) hH hanti

/-- Every endomorphism splits, up to the factor two, into its components
commuting and anticommuting with the actual regular Peirce involution. The
double-commutator kills the first component and acts by four on the second. -/
theorem regularJ_uPlus_uMinus_doubleComm_sector_decomposition
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    let H := regularJ uPlus uMinus
    let Tcomm := T + H * T * H
    let Tanti := T - H * T * H
    Tcomm + Tanti = 2 • T ∧
    H * Tcomm = Tcomm * H ∧
    H * Tanti = -(Tanti * H) ∧
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H Tcomm = 0 ∧
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm H Tanti =
      4 • Tanti := by
  dsimp
  let H := regularJ uPlus uMinus
  have hH : H * H = 1 := regularJ_uPlus_uMinus_sq
  have hcomm : H * (T + H * T * H) = (T + H * T * H) * H := by
    calc
      H * (T + H * T * H) = H * T + (H * H) * T * H := by noncomm_ring
      _ = H * T + T * H := by rw [hH, one_mul]
      _ = T * H + H * T := by abel
      _ = (T + H * T * H) * H := by
        rw [add_mul, mul_assoc (H * T) H H, hH, mul_one]
  have hanti : H * (T - H * T * H) = -((T - H * T * H) * H) := by
    calc
      H * (T - H * T * H) = H * T - (H * H) * T * H := by noncomm_ring
      _ = H * T - T * H := by rw [hH, one_mul]
      _ = -(T * H - H * T) := by noncomm_ring
      _ = -((T - H * T * H) * H) := by
        rw [sub_mul, mul_assoc (H * T) H H, hH, mul_one]
  refine ⟨?_, hcomm, hanti, ?_, ?_⟩
  · rw [two_smul]
    noncomm_ring
  · exact InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm_eq_zero_of_commutes
      H (T + H * T * H) hcomm
  · exact InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm_eq_four_smul_of_anticommutes
      H (T - H * T * H) hH hanti

/-- The regular `J` operator for the complementary Ell idempotents is left
multiplication by the distinguished split axis. -/
theorem regularJ_uPlus_uMinus_eq_leftRegular_lUnit :
    regularJ uPlus uMinus = leftRegular lUnit := by
  apply LinearMap.ext
  intro X
  change uPlus * X - uMinus * X = lUnit * X
  rw [← InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.sub_mul,
    uPlus_sub_uMinus]

/-- An automorphism fixing the distinguished axis intertwines its regular
`J` action.  This is the precise stabilizer condition under which the
automorphism preserves the Ell Peirce eigenspace splitting. -/
theorem axisFixedAutomorphism_intertwines_regularJ
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (X : CanonicalZorn) :
    regularJ uPlus uMinus
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) X) =
      (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
        (regularJ uPlus uMinus X) := by
  rw [regularJ_uPlus_uMinus_eq_leftRegular_lUnit]
  change lUnit * (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) X =
    (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) (lUnit * X)
  rw [InfoGeometry.Canonical.RealSplitOctonionAut.preserves_mul, h_axis]

/-- Fixing the split axis and the algebra unit fixes both genuine Peirce
idempotents that define the Ell-circular basis. -/
theorem axisFixedAutomorphism_fixes_uPlus_uMinus
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit) :
    (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) uPlus = uPlus ∧
    (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) uMinus = uMinus := by
  constructor
  · change (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      ((1 / 2 : ℝ) • (1 + lUnit)) = (1 / 2 : ℝ) • (1 + lUnit)
    rw [map_smul, map_add,
      InfoGeometry.Canonical.RealSplitOctonionAut.preserves_one, h_axis]
  · change (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      ((1 / 2 : ℝ) • (1 - lUnit)) = (1 / 2 : ℝ) • (1 - lUnit)
    rw [map_smul, map_sub,
      InfoGeometry.Canonical.RealSplitOctonionAut.preserves_one, h_axis]

/-- Every scalar eigenspace of the regular Ell `J` operator is invariant
under automorphisms fixing `lUnit`; in particular this applies to the two
Peirce sectors with eigenvalues `+1` and `-1`. -/
theorem axisFixedAutomorphism_preserves_regularJ_eigenvectors
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (c : ℝ) (X : CanonicalZorn)
    (hX : regularJ uPlus uMinus X = c • X) :
    regularJ uPlus uMinus
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) X) =
      c • (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) X := by
  rw [axisFixedAutomorphism_intertwines_regularJ φ h_axis, hX]
  exact (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ).map_smul c X

/-- In Ell-circular coordinates, an automorphism fixing `lUnit` preserves
the positive Peirce sector supported on basis indices `0..3`. -/
theorem axisFixedAutomorphism_preserves_positive_coordinate_sector
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (x : Coordinate) (hx : ∀ i : Fin 8, 4 ≤ i.val → x i = 0) :
    ∀ i : Fin 8, 4 ≤ i.val →
      coordinateEquiv
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
          (coordinateEquiv.symm x)) i = 0 := by
  have hX : regularJ uPlus uMinus (coordinateEquiv.symm x) = coordinateEquiv.symm x := by
    apply coordinateEquiv.injective
    rw [regularJ_uPlus_uMinus_coordinate_apply]
    funext i
    by_cases hi : i.val < 4
    · simp [hi]
    · have hzero := hx i (Nat.le_of_not_gt hi)
      simp [hi, hzero]
  have hφX := axisFixedAutomorphism_preserves_regularJ_eigenvectors
    φ h_axis 1 (coordinateEquiv.symm x) (by simpa using hX)
  let y : Coordinate := coordinateEquiv
    ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      (coordinateEquiv.symm x))
  have hread : coordinateEquiv
      (regularJ uPlus uMinus
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
          (coordinateEquiv.symm x))) =
      (fun i => if i.val < 4 then y i else -y i) := by
    simpa [y] using regularJ_uPlus_uMinus_coordinate_apply y
  have hfixed : (fun i => if i.val < 4 then y i else -y i) = y := by
    calc
      (fun i => if i.val < 4 then y i else -y i) =
          coordinateEquiv (regularJ uPlus uMinus
            ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
              (coordinateEquiv.symm x))) := hread.symm
      _ = y := by simpa [y] using congrArg coordinateEquiv hφX
  intro i hi
  have hcoord := congrFun hfixed i
  have hi' : ¬ i.val < 4 := by omega
  simp only [hi', ↓reduceIte] at hcoord
  linarith

/-- In Ell-circular coordinates, an automorphism fixing `lUnit` preserves
the negative Peirce sector supported on basis indices `4..7`. -/
theorem axisFixedAutomorphism_preserves_negative_coordinate_sector
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (x : Coordinate) (hx : ∀ i : Fin 8, i.val < 4 → x i = 0) :
    ∀ i : Fin 8, i.val < 4 →
      coordinateEquiv
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
          (coordinateEquiv.symm x)) i = 0 := by
  have hX : regularJ uPlus uMinus (coordinateEquiv.symm x) =
      -coordinateEquiv.symm x := by
    apply coordinateEquiv.injective
    rw [regularJ_uPlus_uMinus_coordinate_apply, map_neg,
      coordinateEquiv.apply_symm_apply]
    funext i
    by_cases hi : i.val < 4
    · have hzero := hx i hi
      simp [hi, hzero]
    · simp [hi]
  have hφX := axisFixedAutomorphism_preserves_regularJ_eigenvectors
    φ h_axis (-1) (coordinateEquiv.symm x) (by simpa using hX)
  let y : Coordinate := coordinateEquiv
    ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      (coordinateEquiv.symm x))
  have hread : coordinateEquiv
      (regularJ uPlus uMinus
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
          (coordinateEquiv.symm x))) =
      (fun i => if i.val < 4 then y i else -y i) := by
    simpa [y] using regularJ_uPlus_uMinus_coordinate_apply y
  have heigen : coordinateEquiv
      (regularJ uPlus uMinus
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
          (coordinateEquiv.symm x))) = -y := by
    have hφXneg : regularJ uPlus uMinus
        ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
          (coordinateEquiv.symm x)) =
        -(φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
          (coordinateEquiv.symm x) := by simpa using hφX
    have h := congrArg coordinateEquiv hφXneg
    rw [map_neg] at h
    simpa [y] using h
  have hfixed : (fun i => if i.val < 4 then y i else -y i) = -y :=
    hread.symm.trans heigen
  intro i hi
  have hcoord := congrFun hfixed i
  simp only [hi, ↓reduceIte, Pi.neg_apply] at hcoord
  linarith

/-- The action of a split-octonion automorphism on the Ell-circular
coordinate carrier, obtained by transporting the actual carrier map through
`coordinateEquiv`. -/
noncomputable def ellCoordinateAutomorphism
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    Module.End ℝ Coordinate where
  toFun x := coordinateEquiv
    ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      (coordinateEquiv.symm x))
  map_add' x y := by
    simp only [coordinateEquiv.symm.map_add,
      (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ).map_add,
      coordinateEquiv.map_add]
  map_smul' r x := by
    simp only [coordinateEquiv.symm.map_smul,
      (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ).map_smul,
      coordinateEquiv.map_smul, RingHom.id_apply]

/-- In Ell-circular coordinates, an automorphism fixing `lUnit` fixes the
positive Peirce basis vector `uPlus`. -/
theorem axisFixedAutomorphism_fixes_uPlus_coordinate
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit) :
    ellCoordinateAutomorphism φ (Pi.single 0 (1 : ℝ)) = Pi.single 0 1 := by
  have hfix := (axisFixedAutomorphism_fixes_uPlus_uMinus φ h_axis).1
  have hframe : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      (frame 0) = frame 0 := by simpa [frame] using hfix
  change coordinateEquiv
    ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      (coordinateEquiv.symm (Pi.single 0 (1 : ℝ)))) = Pi.single 0 1
  rw [coordinateEquiv_symm_single, hframe, coordinateEquiv_apply_frame]

/-- In Ell-circular coordinates, an automorphism fixing `lUnit` fixes the
negative Peirce basis vector `uMinus`. -/
theorem axisFixedAutomorphism_fixes_uMinus_coordinate
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit) :
    ellCoordinateAutomorphism φ (Pi.single 4 (1 : ℝ)) = Pi.single 4 1 := by
  have hfix := (axisFixedAutomorphism_fixes_uPlus_uMinus φ h_axis).2
  have hframe : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      (frame 4) = frame 4 := by simpa [frame] using hfix
  change coordinateEquiv
    ((φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ)
      (coordinateEquiv.symm (Pi.single 4 (1 : ℝ)))) = Pi.single 4 1
  rw [coordinateEquiv_symm_single, hframe, coordinateEquiv_apply_frame]

/-- In the actual Ell-circular basis, an automorphism fixing `lUnit` has a
block diagonal 8-by-8 matrix for the `(+1) ⊕ (-1)` eigenspace split of the
regular `J` operator. Equivalently, it cannot mix coordinates `0..3` with
coordinates `4..7`. -/
theorem axisFixedAutomorphism_coordinateMatrix_cross_sector_zero
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h_axis : (φ : InfoGeometry.Canonical.SplitOctonionAutCandidate ℝ) lUnit = lUnit)
    (i j : Fin 8) (h_cross : (i.val < 4) ≠ (j.val < 4)) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        (ellCoordinateAutomorphism φ) i j = 0 := by
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  change ellCoordinateAutomorphism φ (Pi.single j (1 : ℝ) : Coordinate) i = 0
  unfold ellCoordinateAutomorphism
  by_cases hj : j.val < 4
  · have hzero : ∀ k : Fin 8, 4 ≤ k.val →
        ((Pi.single j (1 : ℝ) : Coordinate) k) = 0 := by
      intro k hk
      have hkj : k ≠ j := by
        intro heq
        subst k
        omega
      simp [Pi.single_apply, hkj]
    have hi : 4 ≤ i.val := by
      by_contra hi
      have hi' : i.val < 4 := Nat.lt_of_not_ge hi
      exact h_cross (by simp [hi', hj])
    exact axisFixedAutomorphism_preserves_positive_coordinate_sector
      φ h_axis (Pi.single j (1 : ℝ) : Coordinate) hzero i hi
  · have hzero : ∀ k : Fin 8, k.val < 4 →
        ((Pi.single j (1 : ℝ) : Coordinate) k) = 0 := by
      intro k hk
      have hkj : k ≠ j := by
        intro heq
        subst k
        omega
      simp [Pi.single_apply, hkj]
    have hi : i.val < 4 := by
      by_contra hi
      have hi' : ¬ i.val < 4 := hi
      exact h_cross (by simp [hi', hj])
    exact axisFixedAutomorphism_preserves_negative_coordinate_sector
      φ h_axis (Pi.single j (1 : ℝ) : Coordinate) hzero i hi

/-- Conjugate an endomorphism of the split-octonion carrier into the actual
Ell-circular coordinate carrier. -/
def ellCoordinateConjugate
    (T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    Module.End ℝ Coordinate :=
  coordinateEquiv.conjAlgEquiv ℝ T

/-- In Ell coordinates, the regular Peirce involution is the coordinate form
of left multiplication by the split axis `lUnit`. -/
theorem ellCoordinate_regularJ_eq_leftAxis :
    ellCoordinateConjugate (regularJ uPlus uMinus) =
      leftCoordinateOperator lUnit := by
  apply LinearMap.ext
  intro x
  change coordinateEquiv
      (regularJ uPlus uMinus (coordinateEquiv.symm x)) =
    leftCoordinateOperator lUnit x
  rw [regularJ_uPlus_uMinus_eq_leftRegular_lUnit,
    coordinateEquiv_leftRegular_apply]
  simp

/-- The quaternion-pair action and the Ell Peirce action are the same
operator after the soldering equivalence. -/
theorem cartesianRegularJ_eq_soldered_regularJ :
    cartesianRegularJ =
      cartesianOperatorConjugate
        (ellCoordinateConjugate (regularJ uPlus uMinus)) := by
  rw [ellCoordinate_regularJ_eq_leftAxis]
  rfl

/-- The actual regular `J` action remains an involution after transport from
the split-octonion carrier to its soldered quaternion-pair coordinates. -/
theorem cartesianRegularJ_sq : cartesianRegularJ * cartesianRegularJ = 1 := by
  have hEll :
      ellCoordinateConjugate (regularJ uPlus uMinus) *
          ellCoordinateConjugate (regularJ uPlus uMinus) = 1 := by
    simpa [ellCoordinateConjugate] using
      congrArg (coordinateEquiv.conjAlgEquiv ℝ) regularJ_uPlus_uMinus_sq
  have hCartesian :=
    congrArg (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ) hEll
  rw [cartesianRegularJ_eq_soldered_regularJ]
  simpa [cartesianOperatorConjugate] using hCartesian

/-- Matrix coefficients of regular `J` in the actual Ell-soldered Cartesian
basis. It is diagonal, with `+1` on the first Peirce sector and `-1` on the
second. -/
theorem ellSolderedCartesian_regularJ_matrixEntry (i j : Fin 8) :
    LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
        cartesianRegularJ i j =
      if i = j then (if i.val < 4 then (1 : ℝ) else -1) else 0 := by
  rw [cartesianRegularJ_eq_soldered_regularJ,
    ellSolderedCartesian_operatorMatrix_entry]
  rw [ellCoordinate_regularJ_eq_leftAxis]
  have hcoord := regularJ_uPlus_uMinus_coordinate_apply
    (Pi.single j (1 : ℝ))
  have hconj := congrArg
    (fun T : Module.End ℝ Coordinate => T (Pi.single j (1 : ℝ)))
    ellCoordinate_regularJ_eq_leftAxis
  have hleft : leftCoordinateOperator lUnit (Pi.single j (1 : ℝ)) =
      fun k => if k.val < 4 then (if k = j then (1 : ℝ) else 0) else
        -(if k = j then (1 : ℝ) else 0) := by
    calc leftCoordinateOperator lUnit (Pi.single j (1 : ℝ))
        = ellCoordinateConjugate (regularJ uPlus uMinus) (Pi.single j 1) := hconj.symm
      _ = _ := by
        simpa [ellCoordinateConjugate, LinearEquiv.conjAlgEquiv_apply,
          Pi.single_apply] using hcoord
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, hleft]
  by_cases hij : i = j
  · subst i
    simp [Pi.single_apply]
  · simp [hij, Pi.single_apply]

/-- Commutator and double-commutator superoperators on endomorphisms of the
coordinate carrier. -/
def ellCoordinateComm (A B : Module.End ℝ Coordinate) :
    Module.End ℝ Coordinate := A * B - B * A

def ellCoordinateDoubleComm (A B : Module.End ℝ Coordinate) :
    Module.End ℝ Coordinate := ellCoordinateComm A (ellCoordinateComm A B)

/-- Commutator of endomorphisms of the quaternion-pair coordinate carrier. -/
def cartesianOperatorComm
    (A B : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates) :
    Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates :=
  A * B - B * A

/-- Double commutator on endomorphisms of the quaternion-pair carrier. -/
def cartesianOperatorDoubleComm
    (A B : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates) :
    Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates :=
  cartesianOperatorComm A (cartesianOperatorComm A B)

/-- The Ell-to-Cartesian soldering conjugacy preserves operator composition
and subtraction, hence intertwines the full double-commutator construction. -/
theorem cartesianOperatorConjugate_doubleComm
    (A B : Module.End ℝ Coordinate) :
    cartesianOperatorConjugate (ellCoordinateDoubleComm A B) =
      cartesianOperatorDoubleComm (cartesianOperatorConjugate A)
        (cartesianOperatorConjugate B) := by
  change (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ)
      (A * (A * B - B * A) - (A * B - B * A) * A) =
    (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ A) *
      ((ellCircularToCartesianCoordinates.conjAlgEquiv ℝ A) *
          (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ B) -
        (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ B) *
          (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ A)) -
      ((ellCircularToCartesianCoordinates.conjAlgEquiv ℝ A) *
          (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ B) -
        (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ B) *
          (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ A)) *
        (ellCircularToCartesianCoordinates.conjAlgEquiv ℝ A)
  simp only [map_sub, map_mul]

/-- The regular `J` double-commutator commutes with the Ell-to-Cartesian
soldering map.  Thus the sector operator computed in Ell coordinates can be
read on the Cartesian carrier by conjugating both its generator and its
argument operator. -/
theorem ellCircularToCartesian_intertwines_regularJ_doubleComm
    (T : Module.End ℝ Coordinate) (x : Coordinate) :
    ellCircularToCartesianCoordinates
        (ellCoordinateDoubleComm
          (ellCoordinateConjugate (regularJ uPlus uMinus)) T x) =
      cartesianOperatorConjugate
        (ellCoordinateDoubleComm
          (ellCoordinateConjugate (regularJ uPlus uMinus)) T)
        (ellCircularToCartesianCoordinates x) := by
  change ellCircularToCartesianCoordinates
      (ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularJ uPlus uMinus)) T x) =
    ellCircularToCartesianCoordinates
      (ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularJ uPlus uMinus)) T
        (ellCircularToCartesianCoordinates.symm
          (ellCircularToCartesianCoordinates x)))
  rw [ellCircularToCartesianCoordinates.symm_apply_apply]

/-- The regular tetraktys double-commutator is the same superoperator after
transport to Ell-circular coordinates. This makes the carrier change
explicit and preserves operator composition. -/
theorem ellCoordinateConjugate_doubleComm
    (H T : InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    ellCoordinateConjugate (doubleComm H T) =
      ellCoordinateDoubleComm
        (ellCoordinateConjugate H) (ellCoordinateConjugate T) := by
  change (coordinateEquiv.conjAlgEquiv ℝ) (doubleComm H T) = _
  simp only [doubleComm, operatorComm, map_sub, map_mul]
  rfl

/-- In this distinguished Peirce pair, the `Φ` regular generator is the
identity on the carrier. -/
theorem regularPhi_uPlus_uMinus_eq_one :
    regularPhi uPlus uMinus = 1 := by
  apply LinearMap.ext
  intro X
  change uPlus * X + uMinus * X = X
  rw [← InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    uPlus_add_uMinus,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul]

/-- The two disjoint coordinate Peirce projections have zero compositions;
this proves the corresponding `V` and `Σ` regular generators vanish. -/
theorem regularLeftProjection_compositions_zero :
    leftRegular uPlus * leftRegular uMinus = 0 ∧
      leftRegular uMinus * leftRegular uPlus = 0 := by
  constructor
  · apply LinearMap.ext
    intro X
    change leftRegular uPlus (leftRegular uMinus X) = 0
    apply coordinateEquiv.injective
    rw [coordinateEquiv_leftRegular_apply, coordinateEquiv_leftRegular_apply]
    rw [leftCoordinateOperator_uMinus_apply, leftCoordinateOperator_uPlus_apply]
    funext i
    by_cases hi : i.val < 4
    · simp [hi, Nat.not_le.mpr hi]
      change (0 : Coordinate) i = coordinateEquiv (0 : CanonicalZorn) i
      exact (congrFun (coordinateEquiv.map_zero) i).symm
    · have hi' : i.val ≥ 4 := Nat.le_of_not_gt hi
      simp [hi, hi']
      change (0 : Coordinate) i = coordinateEquiv (0 : CanonicalZorn) i
      exact (congrFun (coordinateEquiv.map_zero) i).symm
  · apply LinearMap.ext
    intro X
    change leftRegular uMinus (leftRegular uPlus X) = 0
    apply coordinateEquiv.injective
    rw [coordinateEquiv_leftRegular_apply, coordinateEquiv_leftRegular_apply]
    rw [leftCoordinateOperator_uPlus_apply, leftCoordinateOperator_uMinus_apply]
    funext i
    by_cases hi : i.val < 4
    · simp [hi, Nat.not_le.mpr hi]
      change (0 : Coordinate) i = coordinateEquiv (0 : CanonicalZorn) i
      exact (congrFun (coordinateEquiv.map_zero) i).symm
    · have hi' : i.val ≥ 4 := Nat.le_of_not_gt hi
      simp [hi, hi']
      change (0 : Coordinate) i = coordinateEquiv (0 : CanonicalZorn) i
      exact (congrFun (coordinateEquiv.map_zero) i).symm

/-- The anticommutator channel `V` and commutator channel `Σ` both vanish
for the complementary `u₊/u₋` idempotents in the Ell-circular convention. -/
theorem regularV_regularSig_uPlus_uMinus_eq_zero :
    regularV uPlus uMinus = 0 ∧ regularSig uPlus uMinus = 0 := by
  rcases regularLeftProjection_compositions_zero with ⟨hpm, hmp⟩
  exact ⟨by simp [regularV, hpm, hmp], by simp [regularSig, hpm, hmp]⟩

/-- For the distinguished complementary `uPlus/uMinus` pair, the regular
`Φ` generator is the identity and the `V`, `Σ` generators vanish, so all
three induced double-commutator channels vanish. The `J` channel has the
explicit plus/minus coordinate action recorded by
`regularJ_uPlus_uMinus_coordinate_apply`. -/
theorem ellCircular_regularTetraktys_doubleComm_reduction (T :
    InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.EndCZ) :
    ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularPhi uPlus uMinus))
        (ellCoordinateConjugate T) = 0 ∧
    ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularV uPlus uMinus))
        (ellCoordinateConjugate T) = 0 ∧
    ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularSig uPlus uMinus))
        (ellCoordinateConjugate T) = 0 := by
  have hΦ : regularPhi uPlus uMinus = 1 := regularPhi_uPlus_uMinus_eq_one
  have hVS := regularV_regularSig_uPlus_uMinus_eq_zero
  constructor
  · rw [← ellCoordinateConjugate_doubleComm, hΦ]
    simp [InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm,
      InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.operatorComm,
      ellCoordinateConjugate]
  · constructor
    · rw [← ellCoordinateConjugate_doubleComm, hVS.1]
      simp [InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm,
        InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.operatorComm,
        ellCoordinateConjugate]
    · rw [← ellCoordinateConjugate_doubleComm, hVS.2]
      simp [InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.doubleComm,
        InfoGeometry.Lie.SplitOctonionTetraktysAutomorphismCovariance.operatorComm,
        ellCoordinateConjugate]

/-- The other three distinguished regular Tetraktys channels remain zero
after transport to the quaternion-pair operator carrier.  This holds for an
arbitrary Cartesian-coordinate endomorphism argument, since the transported
generators themselves are the identity (`Φ`) or zero (`V`, `Σ`). -/
theorem cartesian_regularTetraktys_doubleComm_reduction
    (T : Module.End ℝ Coordinate) :
    cartesianOperatorDoubleComm
        (cartesianOperatorConjugate
          (ellCoordinateConjugate (regularPhi uPlus uMinus)))
        (cartesianOperatorConjugate T) = 0 ∧
    cartesianOperatorDoubleComm
        (cartesianOperatorConjugate
          (ellCoordinateConjugate (regularV uPlus uMinus)))
        (cartesianOperatorConjugate T) = 0 ∧
    cartesianOperatorDoubleComm
        (cartesianOperatorConjugate
          (ellCoordinateConjugate (regularSig uPlus uMinus)))
        (cartesianOperatorConjugate T) = 0 := by
  have hΦ : ellCoordinateConjugate (regularPhi uPlus uMinus) = 1 := by
    rw [regularPhi_uPlus_uMinus_eq_one]
    simp [ellCoordinateConjugate]
  have hVS := regularV_regularSig_uPlus_uMinus_eq_zero
  have hV : ellCoordinateConjugate (regularV uPlus uMinus) = 0 := by
    rw [hVS.1]
    simp [ellCoordinateConjugate]
  have hS : ellCoordinateConjugate (regularSig uPlus uMinus) = 0 := by
    rw [hVS.2]
    simp [ellCoordinateConjugate]
  constructor
  · rw [← cartesianOperatorConjugate_doubleComm, hΦ]
    simp [ellCoordinateDoubleComm, ellCoordinateComm, cartesianOperatorConjugate]
  constructor
  · rw [← cartesianOperatorConjugate_doubleComm, hV]
    simp [ellCoordinateDoubleComm, ellCoordinateComm, cartesianOperatorConjugate]
  · rw [← cartesianOperatorConjugate_doubleComm, hS]
    simp [ellCoordinateDoubleComm, ellCoordinateComm, cartesianOperatorConjugate]

/-- The transported `Φ`, `V`, and `Σ` double-commutator channels vanish on
every Cartesian-coordinate endomorphism, including operators that are not
presented as solderings of Ell-coordinate endomorphisms. -/
theorem cartesian_regularTetraktys_doubleComm_reduction_all
    (T : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates) :
    cartesianOperatorDoubleComm
        (cartesianOperatorConjugate
          (ellCoordinateConjugate (regularPhi uPlus uMinus))) T = 0 ∧
    cartesianOperatorDoubleComm
        (cartesianOperatorConjugate
          (ellCoordinateConjugate (regularV uPlus uMinus))) T = 0 ∧
    cartesianOperatorDoubleComm
        (cartesianOperatorConjugate
          (ellCoordinateConjugate (regularSig uPlus uMinus))) T = 0 := by
  have hΦ : cartesianOperatorConjugate
      (ellCoordinateConjugate (regularPhi uPlus uMinus)) = 1 := by
    rw [regularPhi_uPlus_uMinus_eq_one]
    simp [ellCoordinateConjugate, cartesianOperatorConjugate]
  have hV : cartesianOperatorConjugate
      (ellCoordinateConjugate (regularV uPlus uMinus)) = 0 := by
    rw [regularV_regularSig_uPlus_uMinus_eq_zero.1]
    simp [ellCoordinateConjugate, cartesianOperatorConjugate]
  have hS : cartesianOperatorConjugate
      (ellCoordinateConjugate (regularSig uPlus uMinus)) = 0 := by
    rw [regularV_regularSig_uPlus_uMinus_eq_zero.2]
    simp [ellCoordinateConjugate, cartesianOperatorConjugate]
  refine ⟨?_, ?_, ?_⟩
  · rw [hΦ]
    simp [cartesianOperatorDoubleComm, cartesianOperatorComm]
  · rw [hV]
    simp [cartesianOperatorDoubleComm, cartesianOperatorComm]
  · rw [hS]
    simp [cartesianOperatorDoubleComm, cartesianOperatorComm]

/-- The transported regular `J` is the diagonal involution for the Ell
circular Peirce splitting. -/
theorem ellCircular_regularJ_apply (x : Coordinate) :
    ellCoordinateConjugate (regularJ uPlus uMinus) x =
      fun i => if i.val < 4 then x i else -x i := by
  simpa [ellCoordinateConjugate,
    LinearEquiv.conjAlgEquiv_apply] using
      regularJ_uPlus_uMinus_coordinate_apply x

/-- Matrix readout of the four actual regular Tetraktys generators in the
ordered Ell Peirce basis `(u₊, root₊₀, root₊₁, root₊₂,
u₋, root₋₀, root₋₁, root₋₂)`.  The result records the distinct roles of
the generators: `Φ` is identity, `J` is the Peirce sign involution, and the
regular anticommutator and commutator channels `V` and `Σ` vanish for this
orthogonal pair of idempotents. -/
theorem ellCircular_regularTetraktys_coordinateMatrices :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        (ellCoordinateConjugate (regularPhi uPlus uMinus)) = 1 ∧
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        (ellCoordinateConjugate (regularJ uPlus uMinus)) =
      Matrix.diagonal (fun i => if i.val < 4 then (1 : ℝ) else -1) ∧
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        (ellCoordinateConjugate (regularV uPlus uMinus)) = 0 ∧
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        (ellCoordinateConjugate (regularSig uPlus uMinus)) = 0 := by
  have hΦ : ellCoordinateConjugate (regularPhi uPlus uMinus) = 1 := by
    rw [regularPhi_uPlus_uMinus_eq_one]
    simp [ellCoordinateConjugate]
  have hV : ellCoordinateConjugate (regularV uPlus uMinus) = 0 := by
    rw [regularV_regularSig_uPlus_uMinus_eq_zero.1]
    simp [ellCoordinateConjugate]
  have hSig : ellCoordinateConjugate (regularSig uPlus uMinus) = 0 := by
    rw [regularV_regularSig_uPlus_uMinus_eq_zero.2]
    simp [ellCoordinateConjugate]
  have hJ :
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
          (ellCoordinateConjugate (regularJ uPlus uMinus)) =
        Matrix.diagonal (fun i => if i.val < 4 then (1 : ℝ) else -1) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
      ellCircular_regularJ_apply]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, Pi.single_apply]
    · simp [Matrix.diagonal, hij, Pi.single_apply]
  exact ⟨by rw [hΦ]; simp, hJ, by rw [hV]; simp, by rw [hSig]; simp⟩

/-- The double commutator by the regular `J` has eigenvalue zero on
same-sector matrix units and four on cross-sector matrix units. -/
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

/-- Cartesian readout of the regular-`J` double-commutator on a transported
Ell matrix unit.  The target vector is the Cartesian image of the explicit
Ell sector formula: equal Peirce signs are annihilated, opposite signs are
scaled by four. -/
theorem ellCircularToCartesian_regularJ_doubleComm_matrixUnit
    (T : Module.End ℝ Coordinate) (j : Fin 8) :
    cartesianOperatorConjugate
        (ellCoordinateDoubleComm
          (ellCoordinateConjugate (regularJ uPlus uMinus)) T)
        (ellCircularToCartesianCoordinates (Pi.single j (1 : ℝ))) =
      ellCircularToCartesianCoordinates
        (fun k : Fin 8 =>
          if (k.val < 4) = (j.val < 4) then 0 else
            4 * T (Pi.single j (1 : ℝ)) k) := by
  rw [← ellCircularToCartesian_intertwines_regularJ_doubleComm]
  congr 1
  ext k
  exact ellCircular_regularJ_doubleComm_matrixUnit T k j

/-- Actual matrix-entry law for the regular-`J` double-commutator in the
soldered Cartesian basis.  This is the coordinate-matrix version of the
Ell-sector calculation, with both bases and the operator on the Cartesian
quaternion-pair carrier. -/
theorem ellSolderedCartesian_regularJ_doubleComm_matrixEntry
    (T : Module.End ℝ Coordinate) (i j : Fin 8) :
    LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
        (cartesianOperatorConjugate
          (ellCoordinateDoubleComm
            (ellCoordinateConjugate (regularJ uPlus uMinus)) T)) i j =
      if (i.val < 4) = (j.val < 4) then 0 else
        4 * T (Pi.single j (1 : ℝ)) i := by
  rw [ellSolderedCartesian_operatorMatrix_entry]
  simpa [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr] using
    ellCircular_regularJ_doubleComm_matrixUnit T i j

/-- On the Cartesian quaternion-pair carrier, the regular-`J` double
commutator is represented in the soldered Ell basis by a Peirce-sector
Schur multiplier: same-sector matrix entries vanish and cross-sector entries
are multiplied by four. Both matrices in this statement act on the same
Cartesian coordinate carrier. -/
theorem cartesian_regularJ_doubleComm_matrixEntry
    (T : Module.End ℝ Coordinate) (i j : Fin 8) :
    LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
        (cartesianOperatorDoubleComm
          (cartesianOperatorConjugate
            (ellCoordinateConjugate (regularJ uPlus uMinus)))
          (cartesianOperatorConjugate T)) i j =
      if (i.val < 4) = (j.val < 4) then 0 else
        4 * LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
          (cartesianOperatorConjugate T) i j := by
  rw [← cartesianOperatorConjugate_doubleComm,
    ellSolderedCartesian_regularJ_doubleComm_matrixEntry,
    ellSolderedCartesian_operatorMatrix_entry]
  by_cases hsector : (i.val < 4) = (j.val < 4)
  · simp [hsector]
  · simp [hsector, LinearMap.toMatrix_apply, Pi.basisFun_apply,
      Pi.basisFun_repr]

/-- The Cartesian Peirce-sector Schur multiplier law holds for every
endomorphism of the Cartesian carrier, not only those supplied in Ell
coordinates. The proof pulls an arbitrary Cartesian endomorphism back along
the soldering equivalence and applies the already established basis readout. -/
theorem cartesian_regularJ_doubleComm_matrixEntry_all
    (T : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates)
    (i j : Fin 8) :
    LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
        (cartesianOperatorDoubleComm cartesianRegularJ
          (cartesianOperatorDoubleComm cartesianRegularJ T)) i j =
      if (i.val < 4) = (j.val < 4) then 0 else
        4 * LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
          (cartesianOperatorDoubleComm cartesianRegularJ T) i j := by
  let e := ellCircularToCartesianCoordinates.conjAlgEquiv ℝ
  have hback : cartesianOperatorConjugate (e.symm T) = T := e.apply_symm_apply T
  have htransport :
      cartesianOperatorConjugate
          (ellCoordinateDoubleComm
            (ellCoordinateConjugate (regularJ uPlus uMinus)) (e.symm T)) =
        cartesianOperatorDoubleComm cartesianRegularJ T := by
    rw [cartesianOperatorConjugate_doubleComm,
      ← cartesianRegularJ_eq_soldered_regularJ, hback]
  have h := cartesian_regularJ_doubleComm_matrixEntry
    (ellCoordinateDoubleComm
      (ellCoordinateConjugate (regularJ uPlus uMinus)) (e.symm T)) i j
  rw [← cartesianRegularJ_eq_soldered_regularJ] at h
  rw [htransport] at h
  exact h

/-- First-order Cartesian matrix-entry law for the regular-`J`
double-commutator, valid for every endomorphism of the Cartesian carrier. -/
theorem cartesian_regularJ_doubleComm_matrixEntry_once_all
    (T : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates)
    (i j : Fin 8) :
    LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis
        (cartesianOperatorDoubleComm cartesianRegularJ T) i j =
      if (i.val < 4) = (j.val < 4) then 0 else
        4 * LinearMap.toMatrix ellSolderedCartesianBasis ellSolderedCartesianBasis T i j := by
  let e := ellCircularToCartesianCoordinates.conjAlgEquiv ℝ
  have hback : cartesianOperatorConjugate (e.symm T) = T := e.apply_symm_apply T
  have h := cartesian_regularJ_doubleComm_matrixEntry (e.symm T) i j
  rw [← cartesianRegularJ_eq_soldered_regularJ, hback] at h
  exact h

/-- Full coordinate readout of the double-commutator channel.  Its matrix
coefficient from input sector `j` to output sector `i` is multiplied by four
exactly when the two Peirce signs differ; same-sector coefficients are killed.
This extends the matrix-unit calculation to every input vector. -/
theorem ellCircular_regularJ_doubleComm_apply (T : Module.End ℝ Coordinate)
    (x : Coordinate) (i : Fin 8) :
    ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) T x i =
      4 * ∑ j : Fin 8,
        (if (i.val < 4) = (j.val < 4) then 0 else
          T (Pi.single j (1 : ℝ)) i * x j) := by
  have hx : x = ∑ j : Fin 8, x j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [LinearMap.map_smul]
  rw [Finset.sum_apply]
  calc
    (∑ j : Fin 8,
        (x j • ellCoordinateDoubleComm
          (ellCoordinateConjugate (regularJ uPlus uMinus)) T
          (Pi.single j (1 : ℝ))) i) =
      ∑ j : Fin 8, 4 *
        (if (i.val < 4) = (j.val < 4) then 0 else
          T (Pi.single j (1 : ℝ)) i * x j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Pi.smul_apply, smul_eq_mul]
            rw [ellCircular_regularJ_doubleComm_matrixUnit]
            by_cases hsame : (i.val < 4) = (j.val < 4) <;>
              simp [hsame, smul_eq_mul] <;> ring
    _ = 4 * ∑ j : Fin 8,
        (if (i.val < 4) = (j.val < 4) then 0 else
          T (Pi.single j (1 : ℝ)) i * x j) := by rw [Finset.mul_sum]

/-- The kernel of the regular-`J` double commutator consists exactly of
endomorphisms with no matrix coefficients between the two Peirce sectors.
Thus the zero eigenspace is the block-diagonal operator subspace in the
actual Ell basis. -/
theorem ellCircular_regularJ_doubleComm_eq_zero_iff
    (T : Module.End ℝ Coordinate) :
    ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) T = 0 ↔
      ∀ i j : Fin 8, (i.val < 4) ≠ (j.val < 4) →
        T (Pi.single j (1 : ℝ)) i = 0 := by
  constructor
  · intro h i j hsector
    have hentry := congrFun
      (congrArg (fun F : Module.End ℝ Coordinate => F (Pi.single j (1 : ℝ))) h) i
    rw [ellCircular_regularJ_doubleComm_matrixUnit] at hentry
    have hscaled : (4 : ℝ) * T (Pi.single j (1 : ℝ)) i = 0 := by
      simpa [hsector] using hentry
    exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)
  · intro h
    apply LinearMap.ext
    intro x
    funext i
    rw [ellCircular_regularJ_doubleComm_apply]
    have hsum : ∀ j : Fin 8,
        (if (i.val < 4) = (j.val < 4) then 0 else
          T (Pi.single j (1 : ℝ)) i * x j) = 0 := by
      intro j
      by_cases hij : (i.val < 4) = (j.val < 4)
      · simp [hij]
      · simp [hij, h i j hij]
    rw [Finset.sum_eq_zero (fun j _ => hsum j)]
    simp

/-- The Ell-coordinate regular-`J` double commutator satisfies the exact
polynomial identity `D² = 4D`. The proof uses its matrix-unit readout, so it
depends on the actual Peirce-sector action rather than an abstract expansion
of nested commutators. -/
theorem ellCircular_regularJ_doubleComm_square (T : Module.End ℝ Coordinate) :
    ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus))
        (ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) T) =
      4 • ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) T := by
  apply LinearMap.ext
  intro x
  funext i
  rw [ellCircular_regularJ_doubleComm_apply
      (ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) T) x i]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [ellCircular_regularJ_doubleComm_apply T x i]
  have hsum :
      ∑ j : Fin 8, (if (i.val < 4) = (j.val < 4) then 0 else
        (4 * T (Pi.single j (1 : ℝ)) i) * x j) =
      4 * ∑ j : Fin 8, (if (i.val < 4) = (j.val < 4) then 0 else
        T (Pi.single j (1 : ℝ)) i * x j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hsame : (i.val < 4) = (j.val < 4)
    · simp [hsame]
    · simp [hsame]
      ring
  have hbasis (j : Fin 8) :
      ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) T
          (Pi.single j (1 : ℝ)) i =
        if (i.val < 4) = (j.val < 4) then 0 else
          4 * T (Pi.single j (1 : ℝ)) i := by
    exact ellCircular_regularJ_doubleComm_matrixUnit T i j
  rw [Finset.sum_congr rfl (fun j _ => ?_)]
  · rw [hsum]
    ring
  · rw [hbasis]
    by_cases hsame : (i.val < 4) = (j.val < 4) <;> simp [hsame] <;> ring

/-- The arbitrary-input Cartesian matrix-entry law determines the full
endomorphism identity: the regular-`J` double commutator squares to four
times itself on the Cartesian carrier. -/
theorem cartesian_regularJ_doubleComm_square_all
    (T : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates) :
    cartesianOperatorDoubleComm cartesianRegularJ
        (cartesianOperatorDoubleComm cartesianRegularJ T) =
      4 • cartesianOperatorDoubleComm cartesianRegularJ T := by
  let e := ellCircularToCartesianCoordinates.conjAlgEquiv ℝ
  let U : Module.End ℝ Coordinate := e.symm T
  have hback : cartesianOperatorConjugate U = T := e.apply_symm_apply T
  have hEll := ellCircular_regularJ_doubleComm_square U
  have hMapped := congrArg e hEll
  change cartesianOperatorConjugate
      (ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularJ uPlus uMinus))
        (ellCoordinateDoubleComm
          (ellCoordinateConjugate (regularJ uPlus uMinus)) U)) =
    cartesianOperatorConjugate
      (4 • ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularJ uPlus uMinus)) U) at hMapped
  rw [cartesianOperatorConjugate_doubleComm] at hMapped
  have htransport :
      cartesianOperatorConjugate
          (ellCoordinateDoubleComm
            (ellCoordinateConjugate (regularJ uPlus uMinus)) U) =
        cartesianOperatorDoubleComm cartesianRegularJ T := by
    rw [cartesianOperatorConjugate_doubleComm,
      ← cartesianRegularJ_eq_soldered_regularJ, hback]
  rw [← cartesianRegularJ_eq_soldered_regularJ, htransport] at hMapped
  change cartesianOperatorDoubleComm cartesianRegularJ
      (cartesianOperatorDoubleComm cartesianRegularJ T) =
    e.toLinearEquiv (4 • ellCoordinateDoubleComm
      (ellCoordinateConjugate (regularJ uPlus uMinus)) U) at hMapped
  have htransport' : e.toLinearEquiv
      (ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) U) =
      cartesianOperatorDoubleComm cartesianRegularJ T := by
    change cartesianOperatorConjugate
      (ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) U) = _
    exact htransport
  have hsmul : e.toLinearEquiv
      (4 • ellCoordinateDoubleComm
        (ellCoordinateConjugate (regularJ uPlus uMinus)) U) =
      4 • e.toLinearEquiv
        (ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) U) := by
    exact e.toLinearEquiv.toLinearMap.toAddMonoidHom.map_nsmul 4 _
  calc
    cartesianOperatorDoubleComm cartesianRegularJ
        (cartesianOperatorDoubleComm cartesianRegularJ T) =
        e.toLinearEquiv (4 • ellCoordinateDoubleComm
          (ellCoordinateConjugate (regularJ uPlus uMinus)) U) := hMapped
    _ = 4 • e.toLinearEquiv
        (ellCoordinateDoubleComm (ellCoordinateConjugate (regularJ uPlus uMinus)) U) := hsmul
    _ = 4 • cartesianOperatorDoubleComm cartesianRegularJ T :=
      congrArg (fun X => 4 • X) htransport'

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

/-- The left-regular operator in the Ell frame determines its defining
native Zorn element. Evaluate the transported action at the coordinate vector
of the unit, then use injectivity of `coordinateEquiv` and the native right
unit law. -/
theorem leftCoordinateOperator_injective :
    Function.Injective leftCoordinateOperator := by
  intro A B h
  have h₁ := congrArg (fun T : Module.End ℝ Coordinate =>
    T (coordinateEquiv (1 : CanonicalZorn))) h
  rw [← coordinateEquiv_leftRegular_apply A 1,
    ← coordinateEquiv_leftRegular_apply B 1] at h₁
  have hab : A * (1 : CanonicalZorn) = B * (1 : CanonicalZorn) :=
    coordinateEquiv.injective h₁
  simpa only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one] using hab

/-- The complete `8 × 8` operator matrix in the actual Ell-circular basis is
also a faithful readout of the native left multiplier. -/
theorem leftCoordinateOperatorMatrix_injective :
    Function.Injective leftCoordinateOperatorMatrix := by
  intro A B h
  apply leftCoordinateOperator_injective
  apply (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))).injective
  simpa [leftCoordinateOperatorMatrix] using h

/-- Explicit reconstruction of the native multiplier from its Ell-basis
matrix: applying the matrix to the coordinate vector of the unit returns the
coordinate vector of the multiplier itself. -/
theorem leftCoordinateOperatorMatrix_mulVec_unit (A : CanonicalZorn) :
    Matrix.mulVec (leftCoordinateOperatorMatrix A) (coordinateEquiv (1 : CanonicalZorn)) =
      coordinateEquiv A := by
  have h : Matrix.mulVec (leftCoordinateOperatorMatrix A)
      (coordinateEquiv (1 : CanonicalZorn)) =
      leftCoordinateOperator A (coordinateEquiv (1 : CanonicalZorn)) := by
    simpa [leftCoordinateOperatorMatrix] using
      (LinearMap.toMatrix_mulVec_repr
        (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
        (leftCoordinateOperator A) (coordinateEquiv (1 : CanonicalZorn)))
  rw [← coordinateEquiv_leftRegular_apply A 1] at h
  simpa only [leftRegular_apply,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one] using h

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
