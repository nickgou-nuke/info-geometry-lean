import InfoGeometry.QuantumContext.MassAsCommutantCoupling
import InfoGeometry.Routing.FiniteSoftmax

noncomputable section

namespace InfoGeometry.QuantumContext.TransformerLatentSpace

open InfoGeometry.Routing.FiniteSoftmax
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.MassAsCommutantCoupling

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

def softmaxAttention (scores : Mat2) : Mat2 :=
  fun row column => weight (scores row) 1 column

theorem softmaxAttention_pos (scores : Mat2) (row column : Fin 2) :
    0 < softmaxAttention scores row column :=
  weight_pos (scores row) 1 column

theorem softmaxAttention_row_sum (scores : Mat2) (row : Fin 2) :
    ∑ column, softmaxAttention scores row column = 1 :=
  weight_sum_one (scores row) 1

def leftProjection : Mat2 := !![1, 0; 0, 0]

theorem leftProjection_idempotent : IsIdempotentElem leftProjection := by
  change leftProjection * leftProjection = leftProjection
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [leftProjection, Matrix.mul_apply, Fin.sum_univ_two]

theorem softmaxAttention_not_off_diagonal (scores : Mat2) :
    leftProjection * softmaxAttention scores * leftProjection ≠ 0 := by
  intro vanishes
  have entry := congrArg (fun matrix : Mat2 => matrix 0 0) vanishes
  have zero_entry : softmaxAttention scores 0 0 = 0 := by
    simpa [leftProjection, Matrix.mul_apply, Fin.sum_univ_two] using entry
  exact (softmaxAttention_pos scores 0 0).ne' zero_entry

theorem softmaxAttention_not_swap (scores : Mat2) :
    leftProjection * softmaxAttention scores ≠
      softmaxAttention scores * complementIdempotent leftProjection := by
  intro swap
  exact softmaxAttention_not_off_diagonal scores
    (diagonal_corner_zero leftProjection (softmaxAttention scores) leftProjection_idempotent swap)

theorem zero_scores_weight (row column : Fin 2) :
    softmaxAttention 0 row column = 1 / 2 := by
  norm_num [softmaxAttention, weight, partitionZ, Fin.sum_univ_two]

theorem zero_scores_square_entry (row column : Fin 2) :
    (softmaxAttention 0 * softmaxAttention 0) row column = 1 / 2 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, zero_scores_weight]
  norm_num

theorem zero_scores_square_not_scalar (scalar : ℝ) :
    softmaxAttention 0 * softmaxAttention 0 ≠ scalar • (1 : Mat2) := by
  intro scalar_square
  have entry := congrArg (fun matrix : Mat2 => matrix 0 1) scalar_square
  norm_num [zero_scores_square_entry, Matrix.one_apply] at entry

theorem diagonal_does_not_force_anticommutation :
    (1 : Mat2) * softmaxAttention 0 + softmaxAttention 0 * 1 ≠ 0 := by
  intro anticommutes
  have entry := congrArg (fun matrix : Mat2 => matrix 0 0) anticommutes
  norm_num [zero_scores_weight] at entry

end InfoGeometry.QuantumContext.TransformerLatentSpace
