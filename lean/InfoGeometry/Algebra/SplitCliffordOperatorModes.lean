import InfoGeometry.Algebra.SplitQuaternionMatrices
import InfoGeometry.Geometry.MoebiusChiralGeneratorClassification
import InfoGeometry.Physics.HestenesKreinOperatorCalculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

noncomputable section

namespace InfoGeometry.Algebra.SplitCliffordOperatorModes

open scoped Matrix Matrix.Norms.Operator
open SplitQuaternionMatrices
open InfoGeometry.Geometry.MoebiusChiralGeneratorClassification
open InfoGeometry.Physics.HestenesKreinOperatorCalculus

theorem anticommuting_product_sq {Carrier : Type*} [Ring Carrier]
    (elliptic split : Carrier) (helliptic : elliptic * elliptic = -1)
    (hsplit : split * split = 1) (hanti : elliptic * split = -(split * elliptic)) :
    (elliptic * split) ^ 2 = 1 := by
  have hreverse : split * elliptic = -(elliptic * split) := by
    rw [hanti, neg_neg]
  calc
    (elliptic * split) ^ 2 = elliptic * (split * elliptic) * split := by
      simp only [pow_two, mul_assoc]
    _ = -((elliptic * elliptic) * (split * split)) := by
      rw [hreverse]
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = 1 := by rw [helliptic, hsplit]; simp

theorem anticommuting_product_conjugates {Carrier : Type*} [Ring Carrier]
    (elliptic split : Carrier) (helliptic : elliptic * elliptic = -1)
    (hsplit : split * split = 1) :
    (elliptic * split) * elliptic * (elliptic * split) = -elliptic := by
  calc
    (elliptic * split) * elliptic * (elliptic * split) =
        elliptic * split * (elliptic * elliptic) * split := by
      simp only [mul_assoc]
    _ = -elliptic := by simp [helliptic, mul_assoc, hsplit]

theorem split_mixed_square (angle rapidity : ℝ) :
    (angle • sqI + rapidity • sqJ) ^ 2 =
      (rapidity ^ 2 - angle ^ 2) • (1 : FiniteSpin.Mat2R) := by
  apply anticommuting_mixed_square
  · simp [pow_two]
  · simp [pow_two]
  · simp

theorem split_null_exponential (angle rapidity : ℝ)
    (hnull : rapidity ^ 2 = angle ^ 2) :
    NormedSpace.exp (angle • sqI + rapidity • sqJ) =
      1 + (angle • sqI + rapidity • sqJ) := by
  exact exp_anticommuting_null sqI sqJ (by simp [pow_two])
    (by simp [pow_two]) (by simp) angle rapidity hnull

theorem null_pair_identification :
    (1 / 2 : ℝ) • (sqI + sqJ) = NPlus ∧
      (1 / 2 : ℝ) • (-sqI + sqJ) = NMinus := by
  constructor <;> ext row column <;>
    fin_cases row <;> fin_cases column <;>
    norm_num [sqI, sqJ, NPlus, NMinus]

theorem null_pair_anticommutator : NPlus * NMinus + NMinus * NPlus = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [NPlus, NMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem positive_projector_not_square_zero : Pplus * Pplus ≠ 0 := by
  rw [Pplus_idempotent]
  intro hequal
  have hentry := congrArg (fun matrix : FiniteSpin.Mat2R => matrix 0 0) hequal
  norm_num [Pplus, sqJ] at hentry

theorem complementary_projectors_not_CAR : Pplus * Pminus + Pminus * Pplus ≠ 1 := by
  simp

theorem mixed_generator_discriminant (angle rapidity : ℝ) :
    Matrix.trace (angle • sqI + rapidity • sqJ) ^ 2 -
      4 * (angle • sqI + rapidity • sqJ).det =
        4 * (rapidity ^ 2 - angle ^ 2) := by
  simp [sqI, sqJ, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

end InfoGeometry.Algebra.SplitCliffordOperatorModes
