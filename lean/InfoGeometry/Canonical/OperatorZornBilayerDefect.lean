import InfoGeometry.Canonical.OperatorZornRealModule
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge
import InfoGeometry.Projective.PositiveOperatorExpectation

/-!
# Full bilayer square on the nonassociative operator-Zorn module

`D` is an arbitrary native real-linear endomorphism. Its commutator with left
coupling is retained; it is NOT assumed to be a derivation. Only the separate
specialization to the already owned coefficient derivation uses Leibniz.
Composition of linear maps is not identified with the native Zorn product.
The associator is retained in the square and in its normalized readout.
-/

noncomputable section
namespace InfoGeometry.Canonical.OperatorZornBilayerDefect

open InfoGeometry.Physics.NCG
open OperatorZornRealModule OperatorZornFourPotentialGauge

variable {A : Type*} [Ring A] [Algebra ℝ A]

local notation "Z" => OperatorZornMatrix A

/-- Left coupling acts on the existing carrier; it is not a multiplicative representation. -/
def leftCoupling (gap : Z) : Z →ₗ[ℝ] Z where
  toFun X := gap * X
  map_add' X Y := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals dsimp [NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
    all_goals noncomm_ring
  map_smul' c X := zorn_mul_smul c gap X

/-- Mixed left actions retain their exact associator defect. -/
theorem leftCoupling_comp_apply (upper lower X : Z) :
    leftCoupling upper (leftCoupling lower X) =
      (upper * lower) * X - associator upper lower X := by
  change upper * (lower * X) =
    (upper * lower) * X - ((upper * lower) * X - upper * (lower * X))
  abel

/-- The correction is exact without alternativity or an associative quotient. -/
theorem leftCoupling_square_apply (gap X : Z) :
    leftCoupling gap (leftCoupling gap X) = (gap * gap) * X - associator gap gap X :=
  leftCoupling_comp_apply gap gap X

/-- The full gap commutator is an operator, not an assumed derivative of the gap. -/
def gapCommutator (D : Z →ₗ[ℝ] Z) (gap : Z) : Z →ₗ[ℝ] Z :=
  D.comp (leftCoupling gap) - (leftCoupling gap).comp D

/-- Independent ordered sheet couplings on two copies of the same Zorn module.
No adjoint identification or equality of the two couplings is imposed. -/
def twoSidedBilayer (D : Z →ₗ[ℝ] Z) (upper lower : Z) : (Z × Z) →ₗ[ℝ] (Z × Z) where
  toFun XY := (D XY.1 + leftCoupling upper XY.2, leftCoupling lower XY.1 - D XY.2)
  map_add' XY UV := by
    apply Prod.ext
    · change D (XY.1 + UV.1) + leftCoupling upper (XY.2 + UV.2) = _
      rw [map_add, map_add]
      change (D XY.1 + D UV.1) + (leftCoupling upper XY.2 + leftCoupling upper UV.2) =
        (D XY.1 + leftCoupling upper XY.2) + (D UV.1 + leftCoupling upper UV.2)
      abel
    · change leftCoupling lower (XY.1 + UV.1) - D (XY.2 + UV.2) = _
      rw [map_add, map_add]
      change (leftCoupling lower XY.1 + leftCoupling lower UV.1) - (D XY.2 + D UV.2) =
        (leftCoupling lower XY.1 - D XY.2) + (leftCoupling lower UV.1 - D UV.2)
      abel
  map_smul' c XY := by
    apply Prod.ext
    · change D (c • XY.1) + leftCoupling upper (c • XY.2) =
        c • (D XY.1 + leftCoupling upper XY.2)
      rw [map_smul, map_smul, smul_add]
    · change leftCoupling lower (c • XY.1) - D (c • XY.2) =
        c • (leftCoupling lower XY.1 - D XY.2)
      rw [map_smul, map_smul, smul_sub]

/-- Equal couplings reproduce the attachment's bilayer without changing the product. -/
def bilayer (D : Z →ₗ[ℝ] Z) (gap : Z) : (Z × Z) →ₗ[ℝ] (Z × Z) :=
  twoSidedBilayer D gap gap

/-- The two ordered gap products, two associators, and two operator commutators remain. -/
theorem twoSidedBilayer_square (D : Z →ₗ[ℝ] Z) (upper lower X Y : Z) :
    twoSidedBilayer D upper lower (twoSidedBilayer D upper lower (X,Y)) =
      (D (D X) + (upper*lower)*X - associator upper lower X + gapCommutator D upper Y,
       D (D Y) + (lower*upper)*Y - associator lower upper Y - gapCommutator D lower X) := by
  apply Prod.ext
  · change D (D X + leftCoupling upper Y) + leftCoupling upper (leftCoupling lower X - D Y) =
      D (D X) + (upper*lower)*X - associator upper lower X +
        (D (leftCoupling upper Y) - leftCoupling upper (D Y))
    rw [map_add, map_sub, leftCoupling_comp_apply]
    abel
  · change leftCoupling lower (D X + leftCoupling upper Y) - D (leftCoupling lower X - D Y) =
      D (D Y) + (lower*upper)*Y - associator lower upper Y -
        (D (leftCoupling lower X) - leftCoupling lower (D X))
    rw [map_add, map_sub, leftCoupling_comp_apply]
    abel

/-- The attachment's equal-gap specialization retains all corrections. -/
theorem bilayer_square (D : Z →ₗ[ℝ] Z) (gap X Y : Z) :
    bilayer D gap (bilayer D gap (X,Y)) =
      (D (D X) + (gap*gap)*X - associator gap gap X + gapCommutator D gap Y,
       D (D Y) + (gap*gap)*Y - associator gap gap Y - gapCommutator D gap X) :=
  twoSidedBilayer_square D gap gap X Y

/-- Bundle the existing coefficient derivation, without changing its definition. -/
def internalDerivative (p : A) : Z →ₗ[ℝ] Z where
  toFun := coefficientDeriv p
  map_add' X Y := coefficientDeriv_add p X Y
  map_smul' c X := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals dsimp [coefficientDeriv, coefficientBracket, operatorZornCoordinates]
    all_goals simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Leibniz identifies the gap commutator only for this actual derivation. -/
theorem gapCommutator_internalDerivative (p : A) (gap X : Z) :
    gapCommutator (internalDerivative p) gap X = coefficientDeriv p gap * X := by
  change coefficientDeriv p (gap * X) - gap * coefficientDeriv p X = _
  rw [coefficientDeriv_mul]
  abel

/-- The specialized formula retains the derivative-of-gap term and both associators. -/
theorem bilayer_internalDerivative_square (p : A) (gap X Y : Z) :
    bilayer (internalDerivative p) gap (bilayer (internalDerivative p) gap (X,Y)) =
      (coefficientDeriv p (coefficientDeriv p X) + (gap*gap)*X - associator gap gap X +
         coefficientDeriv p gap * Y,
       coefficientDeriv p (coefficientDeriv p Y) + (gap*gap)*Y - associator gap gap Y -
         coefficientDeriv p gap * X) := by
  simpa only [gapCommutator_internalDerivative] using
    bilayer_square (internalDerivative p) gap X Y

/-- The attachment's plain sheet swap has a coupling anticommutator, not automatic
particle-hole covariance. The swap is Mathlib's actual product equivalence. -/
theorem sheetSwap_anticommutator (D : Z →ₗ[ℝ] Z) (gap X Y : Z) :
    bilayer D gap ((LinearEquiv.prodComm ℝ Z Z) (X,Y)) +
      (LinearEquiv.prodComm ℝ Z Z) (bilayer D gap (X,Y)) =
        (gap*X + gap*X, gap*Y + gap*Y) := by
  apply Prod.ext
  · change (D Y + gap*X) + (gap*X - D Y) = gap*X + gap*X
    abel
  · change (gap*Y - D X) + (D X + gap*Y) = gap*Y + gap*Y
    abel

/-- The two nonzero diagonal poles already disprove a gap from mere nonzero coupling. -/
theorem pole_zeroMode :
    bilayer (0 : Z →ₗ[ℝ] Z) (nPlus 1) (nMinus 1, 0) = (0,0) := by
  apply Prod.ext
  all_goals apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [bilayer, twoSidedBilayer, leftCoupling, nPlus, nMinus, NCZornElement.mul,
    NCZornElement.zornDot, NCZornElement.zornCross]

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

/-- The parent's positive normalized expectation detects the actual action-square
correction. It is not the associator of a product of scalar expectations. -/
theorem leftCoupling_square_defect_expectation :
    (readout (ray twoWeights) diagonalState
      (leftCoupling (curvedZorn * curvedZorn) (nPlus 1) -
        leftCoupling curvedZorn (leftCoupling curvedZorn (nPlus 1)))).sigma_minus 2 =
      (1/3 : ℝ) := by
  exact associator_expectation_one_third

end InfoGeometry.Projective.PositiveOperatorExpectation
