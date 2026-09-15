import InfoGeometry.Spectrometry.FixedScaleLeastSquares

namespace InfoGeometry.Spectrometry.MatrixFixedScaleLeastSquares

open scoped BigOperators
open Finset FixedScaleLeastSquares SvdClrEquivalence

noncomputable section

variable {rowCount acquisitionCount : ℕ}

def matrixSquaredDistance
    (first second : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ) : ℝ :=
  ∑ row, ∑ acquisition, (first row acquisition - second row acquisition) ^ 2

def totalLoss (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ) : ℝ :=
  ∑ row, rowLoss (observed row) scales (profile row)

theorem total_loss_eq_matrix_squared_distance
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ) :
    totalLoss observed scales profile =
      matrixSquaredDistance observed (responseMatrix profile scales) := rfl

theorem total_loss_nonneg
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ) :
    0 ≤ totalLoss observed scales profile :=
  sum_nonneg (fun row _ => sum_nonneg (fun acquisition _ =>
    sq_nonneg (observed row acquisition - profile row * scales acquisition)))

theorem total_loss_zero_scales
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (profile : Fin rowCount → ℝ) :
    totalLoss observed 0 profile = ∑ row, ∑ acquisition, observed row acquisition ^ 2 := by
  simp [totalLoss, rowLoss]

theorem response_matrix_squared_distance
    (first second : Fin rowCount → ℝ) (scales : Fin acquisitionCount → ℝ) :
    matrixSquaredDistance (responseMatrix first scales) (responseMatrix second scales) =
      scaleSquareSum scales * ∑ row, (first row - second row) ^ 2 := by
  simp only [matrixSquaredDistance, responseMatrix, Matrix.vecMulVec_apply, ← sub_mul, mul_pow]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  exact mul_comm _ _

theorem total_loss_pythagorean
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    totalLoss observed scales profile =
      totalLoss observed scales (optimalProfile observed scales) +
        scaleSquareSum scales * ∑ row, (profile row - optimalProfile observed scales row) ^ 2 := by
  unfold totalLoss
  calc
    (∑ row, rowLoss (observed row) scales (profile row)) =
        ∑ row, (rowLoss (observed row) scales (optimalProfile observed scales row) +
          scaleSquareSum scales * (profile row - optimalProfile observed scales row) ^ 2) :=
      sum_congr rfl (fun row _ => row_loss_pythagorean observed scales row (profile row) norm_ne)
    _ = _ := by rw [sum_add_distrib, ← mul_sum]

theorem matrix_projection_pythagorean
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    matrixSquaredDistance observed (responseMatrix profile scales) =
      matrixSquaredDistance observed (reconstruction observed scales) +
        matrixSquaredDistance (reconstruction observed scales) (responseMatrix profile scales) := by
  rw [reconstruction, response_matrix_squared_distance]
  simp_rw [sub_sq_comm (optimalProfile observed scales _) (profile _)]
  exact total_loss_pythagorean observed scales profile norm_ne

theorem total_loss_minimizes
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    totalLoss observed scales (optimalProfile observed scales) ≤
      totalLoss observed scales profile := by
  rw [total_loss_pythagorean observed scales profile norm_ne]
  exact le_add_of_nonneg_right (mul_nonneg (scale_square_sum_nonneg scales)
    (sum_nonneg (fun row _ => sq_nonneg _)))

theorem optimal_profile_isMinOn
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (norm_ne : scaleSquareSum scales ≠ 0) :
    IsMinOn (totalLoss observed scales) Set.univ (optimalProfile observed scales) :=
  fun profile _ => total_loss_minimizes observed scales profile norm_ne

theorem total_loss_eq_minimum_iff
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    totalLoss observed scales profile =
      totalLoss observed scales (optimalProfile observed scales) ↔
        profile = optimalProfile observed scales := by
  rw [total_loss_pythagorean observed scales profile norm_ne]
  simp only [add_eq_left, mul_eq_zero, norm_ne, false_or]
  rw [sum_eq_zero_iff_of_nonneg (fun row _ => sq_nonneg _)]
  constructor
  · intro vanishes
    funext row
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (vanishes row (mem_univ row)))
  · intro equal row _
    simp [equal]

theorem total_loss_strict_of_ne
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0)
    (different : profile ≠ optimalProfile observed scales) :
    totalLoss observed scales (optimalProfile observed scales) <
      totalLoss observed scales profile := by
  apply lt_of_le_of_ne (total_loss_minimizes observed scales profile norm_ne)
  intro equal
  exact different ((total_loss_eq_minimum_iff observed scales profile norm_ne).mp equal.symm)

theorem total_loss_rescale
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (factor : ℝ) (factor_ne : factor ≠ 0) :
    totalLoss observed (fun acquisition => factor * scales acquisition)
      (fun row => profile row / factor) = totalLoss observed scales profile := by
  unfold totalLoss rowLoss
  apply sum_congr rfl
  intro row _
  apply sum_congr rfl
  intro acquisition _
  dsimp
  rw [← mul_assoc, div_mul_cancel₀ _ factor_ne]

end

end InfoGeometry.Spectrometry.MatrixFixedScaleLeastSquares
