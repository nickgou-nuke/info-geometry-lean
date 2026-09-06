import InfoGeometry.Canonical.OperatorZornRealModule
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge

/-! Bilayer action on the native nonassociative operator-Zorn carrier. -/
noncomputable section
namespace InfoGeometry.Canonical.OperatorZornBilayerDefect

open InfoGeometry.Physics.NCG
open OperatorZornRealModule OperatorZornFourPotentialGauge

variable {A : Type*} [Ring A] [Algebra ℝ A]
local notation "Z" => OperatorZornMatrix A

def leftCoupling (gap : Z) : Z →ₗ[ℝ] Z where
  toFun X := gap * X
  map_add' X Y := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals dsimp [NCZornElement.mul, NCZornElement.zornDot,
      NCZornElement.zornCross]
    all_goals noncomm_ring
  map_smul' c X := zorn_mul_smul c gap X

theorem leftCoupling_comp_apply (upper lower X : Z) :
    leftCoupling upper (leftCoupling lower X) =
      (upper * lower) * X - associator upper lower X := by
  change upper * (lower * X) =
    (upper * lower) * X - ((upper * lower) * X - upper * (lower * X))
  abel

def gapCommutator (D : Z →ₗ[ℝ] Z) (gap : Z) : Z →ₗ[ℝ] Z :=
  D.comp (leftCoupling gap) - (leftCoupling gap).comp D

def twoSidedBilayer (D : Z →ₗ[ℝ] Z) (upper lower : Z) :
    (Z × Z) →ₗ[ℝ] (Z × Z) where
  toFun XY :=
    (D XY.1 + leftCoupling upper XY.2,
      leftCoupling lower XY.1 - D XY.2)
  map_add' XY UV := by
    apply Prod.ext
    · change D (XY.1 + UV.1) + leftCoupling upper (XY.2 + UV.2) = _
      rw [map_add, map_add]
      change (D XY.1 + D UV.1) +
        (leftCoupling upper XY.2 + leftCoupling upper UV.2) = _
      abel
    · change leftCoupling lower (XY.1 + UV.1) - D (XY.2 + UV.2) = _
      rw [map_add, map_add]
      change (leftCoupling lower XY.1 + leftCoupling lower UV.1) -
        (D XY.2 + D UV.2) = _
      abel
  map_smul' c XY := by
    apply Prod.ext
    · change D (c • XY.1) + leftCoupling upper (c • XY.2) = _
      rw [map_smul, map_smul, smul_add]
    · change leftCoupling lower (c • XY.1) - D (c • XY.2) = _
      rw [map_smul, map_smul, smul_sub]

def bilayer (D : Z →ₗ[ℝ] Z) (gap : Z) :
    (Z × Z) →ₗ[ℝ] (Z × Z) := twoSidedBilayer D gap gap

theorem twoSidedBilayer_square (D : Z →ₗ[ℝ] Z) (upper lower X Y : Z) :
    twoSidedBilayer D upper lower (twoSidedBilayer D upper lower (X,Y)) =
      (D (D X) + (upper*lower)*X - associator upper lower X +
          gapCommutator D upper Y,
       D (D Y) + (lower*upper)*Y - associator lower upper Y -
          gapCommutator D lower X) := by
  apply Prod.ext
  · change D (D X + leftCoupling upper Y) +
        leftCoupling upper (leftCoupling lower X - D Y) = _
    rw [map_add, map_sub, leftCoupling_comp_apply]
    abel
  · change leftCoupling lower (D X + leftCoupling upper Y) -
        D (leftCoupling lower X - D Y) = _
    rw [map_add, map_sub, leftCoupling_comp_apply]
    abel

theorem bilayer_square (D : Z →ₗ[ℝ] Z) (gap X Y : Z) :
    bilayer D gap (bilayer D gap (X,Y)) =
      (D (D X) + (gap*gap)*X - associator gap gap X +
          gapCommutator D gap Y,
       D (D Y) + (gap*gap)*Y - associator gap gap Y -
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
  change coefficientDeriv p (gap * X) - gap * coefficientDeriv p X = _
  rw [coefficientDeriv_mul]
  abel

end InfoGeometry.Canonical.OperatorZornBilayerDefect
