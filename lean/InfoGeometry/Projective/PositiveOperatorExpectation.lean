import InfoGeometry.Projective.OperatorZornStateGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A constructed positive coefficient expectation with nonzero Zorn associator

Real matrices are one possible coefficient algebra, not a replacement for
the nonassociative Zorn algebra. Positivity concerns the coefficient state,
not the indefinite split-octonion quadratic norm.
-/

noncomputable section
namespace InfoGeometry.Projective.PositiveOperatorExpectation

open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG
open OperatorZornRealModule OperatorZornFourPotentialGauge
open ExpectationRatioMetric OperatorZornStateGeometry
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Diagonal vector states in a real coefficient matrix algebra. -/
def diagonalState (i : ι) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun M := M i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def operatorExpectation (q : Ray ι) : Matrix ι ι ℝ →ₗ[ℝ] ℝ := evaluation q diagonalState

@[simp] theorem operatorExpectation_one (q : Ray ι) :
    operatorExpectation q (1 : Matrix ι ι ℝ) = 1 := by
  change rayMean q (fun i => (1 : Matrix ι ι ℝ) i i) = 1
  simp [rayMean_const]

theorem operatorExpectation_transpose_mul (q : Ray ι) (M : Matrix ι ι ℝ) :
    operatorExpectation q (M.transpose * M) = rayMean q (fun i => ∑ j, (M j i)^2) := by
  change rayMean q (fun i => (M.transpose * M) i i) = _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem operatorExpectation_positive (q : Ray ι) (M : Matrix ι ι ℝ) :
    0 ≤ operatorExpectation q (M.transpose * M) := by
  rw [operatorExpectation_transpose_mul]
  apply rayMean_nonneg
  intro i
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- A strictly positive nonuniform reference is retained in the witness. -/
def twoWeights : Weight (Fin 2) := ⟨![2,1], by intro i; fin_cases i <;> norm_num⟩

def e12 : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;0,0]
def e21 : Matrix (Fin 2) (Fin 2) ℝ := !![0,0;1,0]
def e11 : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]

/-- Positive expectation is not multiplicative, even in the coefficient algebra. -/
theorem expectation_not_multiplicative :
    operatorExpectation (ray twoWeights) (e11*e11) ≠
      operatorExpectation (ray twoWeights) e11 * operatorExpectation (ray twoWeights) e11 := by
  norm_num [operatorExpectation, evaluation, diagonalState, rayMean, ray, mean,
    weightedSum, twoWeights, PositiveMeasure.Z, e11, Matrix.mul_apply, Fin.sum_univ_two]

def curvedZorn : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℝ) :=
  sigmaPlus ![e12,e21,0]

/-- A genuine nonzero, normalized associator expectation in the full Zorn carrier. -/
theorem associator_expectation_one_third :
    (readout (ray twoWeights) diagonalState
      (OperatorZornFourPotentialGauge.associator curvedZorn curvedZorn (nPlus 1))).sigma_minus 2 = (1/3 : ℝ) := by
  norm_num [readout, coefficientReadout, evaluation, diagonalState,
    rayMean, ray, mean, weightedSum, twoWeights, PositiveMeasure.Z,
    OperatorZornFourPotentialGauge.associator, curvedZorn, nPlus, sigmaPlus, operatorZornCoordinates,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross,
    e12, e21, Matrix.mul_apply, Fin.sum_univ_two, HSub.hSub, Sub.sub]

theorem associator_expectation_ne_zero :
    readout (ray twoWeights) diagonalState
      (OperatorZornFourPotentialGauge.associator curvedZorn curvedZorn (nPlus 1)) ≠ 0 := by
  intro h
  have hv := congrArg (fun Z : OperatorZornMatrix ℝ => Z.sigma_minus 2) h
  dsimp at hv
  rw [associator_expectation_one_third] at hv
  change (1/3 : ℝ) = 0 at hv
  norm_num at hv

end InfoGeometry.Projective.PositiveOperatorExpectation

