import InfoGeometry.Canonical.OperatorZornRealModule
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge
import InfoGeometry.Projective.PositiveOperatorExpectation

/-! Bilayer action on the native nonassociative operator-Zorn carrier. -/
noncomputable section
namespace InfoGeometry.Canonical.OperatorZornBilayerDefect

open InfoGeometry.Physics.NCG
open OperatorZornRealModule OperatorZornFourPotentialGauge

variable {A : Type*} [Ring A] [Algebra ℝ A]
local notation "Z" => OperatorZornMatrix A

def leftCoupling (gap : Z) : Z →ₗ[ℝ] Z where
  toFun X := gap * X
  map_add' X Y := zorn_mul_add_right gap X Y
  map_smul' c X := zorn_mul_smul c gap X

theorem leftCoupling_comp_apply (upper lower X : Z) :
    leftCoupling upper (leftCoupling lower X) =
      (upper * lower) * X - OperatorZornFourPotentialGauge.associator upper lower X := by
  dsimp [leftCoupling, OperatorZornFourPotentialGauge.associator]
  exact (sub_sub_cancel ((upper * lower) * X) (upper * (lower * X))).symm

theorem leftCoupling_square_apply (gap X : Z) :
    leftCoupling gap (leftCoupling gap X) =
      (gap * gap) * X - OperatorZornFourPotentialGauge.associator gap gap X :=
  leftCoupling_comp_apply gap gap X

def gapCommutator (D : Z →ₗ[ℝ] Z) (gap : Z) : Z →ₗ[ℝ] Z :=
  D.comp (leftCoupling gap) - (leftCoupling gap).comp D

def twoSidedBilayer (D : Z →ₗ[ℝ] Z) (upper lower : Z) :
    (Z × Z) →ₗ[ℝ] (Z × Z) where
  toFun XY :=
    (D XY.1 + leftCoupling upper XY.2,
      leftCoupling lower XY.1 - D XY.2)
  map_add' XY UV := by
    apply Prod.ext
    · dsimp
      rw [map_add, map_add]
      abel
    · dsimp
      rw [map_add, map_add]
      abel
  map_smul' c XY := by
    apply Prod.ext
    · dsimp
      rw [map_smul, map_smul, smul_add]
    · dsimp
      rw [map_smul, map_smul, smul_sub]

def bilayer (D : Z →ₗ[ℝ] Z) (gap : Z) :
    (Z × Z) →ₗ[ℝ] (Z × Z) := twoSidedBilayer D gap gap

theorem twoSidedBilayer_square (D : Z →ₗ[ℝ] Z) (upper lower X Y : Z) :
    twoSidedBilayer D upper lower (twoSidedBilayer D upper lower (X,Y)) =
      (D (D X) + (upper*lower)*X - OperatorZornFourPotentialGauge.associator upper lower X +
          gapCommutator D upper Y,
       D (D Y) + (lower*upper)*Y - OperatorZornFourPotentialGauge.associator lower upper Y -
          gapCommutator D lower X) := by
  apply Prod.ext
  · dsimp [twoSidedBilayer, gapCommutator]
    rw [map_add, map_sub, leftCoupling_comp_apply]
    abel
  · dsimp [twoSidedBilayer, gapCommutator]
    rw [map_add, map_sub, leftCoupling_comp_apply]
    abel

theorem bilayer_square (D : Z →ₗ[ℝ] Z) (gap X Y : Z) :
    bilayer D gap (bilayer D gap (X,Y)) =
      (D (D X) + (gap*gap)*X - OperatorZornFourPotentialGauge.associator gap gap X +
          gapCommutator D gap Y,
       D (D Y) + (gap*gap)*Y - OperatorZornFourPotentialGauge.associator gap gap Y -
          gapCommutator D gap X) :=
  twoSidedBilayer_square D gap gap X Y

def internalDerivative (p : A) : Z →ₗ[ℝ] Z where
  toFun := coefficientDeriv p
  map_add' X Y := coefficientDeriv_add p X Y
  map_smul' c X := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals dsimp [coefficientDeriv, coefficientBracket,
      operatorZornCoordinates]
    all_goals simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem gapCommutator_internalDerivative (p : A) (gap X : Z) :
    gapCommutator (internalDerivative p) gap X = coefficientDeriv p gap * X := by
  dsimp [gapCommutator, internalDerivative, leftCoupling]
  rw [coefficientDeriv_mul]
  exact add_sub_cancel_right (coefficientDeriv p gap * X) (gap * coefficientDeriv p X)

theorem bilayer_internalDerivative_square (p : A) (gap X Y : Z) :
    bilayer (internalDerivative p) gap (bilayer (internalDerivative p) gap (X,Y)) =
      (coefficientDeriv p (coefficientDeriv p X) + (gap*gap)*X -
          OperatorZornFourPotentialGauge.associator gap gap X +
          coefficientDeriv p gap * Y,
       coefficientDeriv p (coefficientDeriv p Y) + (gap*gap)*Y -
          OperatorZornFourPotentialGauge.associator gap gap Y -
          coefficientDeriv p gap * X) := by
  simpa only [gapCommutator_internalDerivative] using
    bilayer_square (internalDerivative p) gap X Y

theorem sheetSwap_anticommutator (D : Z →ₗ[ℝ] Z) (gap X Y : Z) :
    bilayer D gap ((LinearEquiv.prodComm ℝ Z Z) (X,Y)) +
      (LinearEquiv.prodComm ℝ Z Z) (bilayer D gap (X,Y)) =
        (gap*X + gap*X, gap*Y + gap*Y) := by
  apply Prod.ext
  · change (D Y + gap*X) + (gap*X - D Y) = gap*X + gap*X
    abel
  · change (gap*Y - D X) + (D X + gap*Y) = gap*Y + gap*Y
    abel

theorem pole_zeroMode :
    bilayer (0 : Z →ₗ[ℝ] Z) (nPlus 1) (nMinus 1, 0) = (0,0) := by
  apply Prod.ext
  all_goals apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [bilayer, twoSidedBilayer, leftCoupling, nPlus, nMinus,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals rfl

theorem nonzero_coupling_has_nonzero_zeroMode [Nontrivial A] :
    (nPlus (1 : A) : Z) ≠ 0 ∧ (nMinus (1 : A), (0 : Z)) ≠ (0,0) ∧
      bilayer (0 : Z →ₗ[ℝ] Z) (nPlus 1) (nMinus 1, 0) = (0,0) := by
  refine ⟨?_, ?_, pole_zeroMode⟩
  · intro h
    have hc := congrArg NCZornElement.n_plus h
    exact one_ne_zero (by simpa [nPlus] using hc)
  · intro h
    have hc := congrArg (fun XY : Z × Z => XY.1.n_minus) h
    exact one_ne_zero (by simpa [nMinus] using hc)

end InfoGeometry.Canonical.OperatorZornBilayerDefect

namespace InfoGeometry.Projective.PositiveOperatorExpectation

open InfoGeometry.Canonical
open OperatorZornBilayerDefect ExpectationRatioMetric OperatorZornStateGeometry

theorem leftCoupling_square_defect_expectation :
    (readout (ray twoWeights) diagonalState
      (leftCoupling (curvedZorn * curvedZorn) (nPlus 1) -
        leftCoupling curvedZorn (leftCoupling curvedZorn (nPlus 1)))).sigma_minus 2 =
      (1/3 : ℝ) := by
  exact associator_expectation_one_third

end InfoGeometry.Projective.PositiveOperatorExpectation
