import InfoGeometry.Epistemology.WheelersSelfObservingUniverse
import InfoGeometry.QuantumContext.TransformerLatentSpace
import InfoGeometry.QuantumContext.ProjectionCouplingDependencies

noncomputable section

namespace InfoGeometry.QuantumContext.ProjectionCouplingTests

open InfoGeometry.Epistemology.WheelersSelfObservingUniverse
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.MassAsCommutantCoupling
open InfoGeometry.QuantumContext.TransformerLatentSpace

def skewProjection : Module.End ℝ (ℝ × ℝ) where
  toFun vector := (vector.1 + vector.2, 0)
  map_add' left right := by ext <;> simp <;> ring
  map_smul' scalar vector := by ext <;> simp [mul_add]

theorem skewProjection_idempotent : IsIdempotentElem skewProjection := by
  change skewProjection * skewProjection = skewProjection
  apply LinearMap.ext
  intro vector
  change (vector.1 + vector.2 + 0, 0) = (vector.1 + vector.2, 0)
  simp

example : skewProjection (1, 0) = (1, 0) := by norm_num [skewProjection]

example : skewProjection (-1, 1) = 0 := by norm_num [skewProjection]

example : (1 : ℝ) * (-1) + 0 * 1 ≠ 0 := by norm_num

example (state : ℝ × ℝ) :
    ∃! components : (ℝ × ℝ) × (ℝ × ℝ),
      skewProjection components.1 = components.1 ∧ skewProjection components.2 = 0 ∧
        components.1 + components.2 = state :=
  exists_unique_decomposition skewProjection skewProjection_idempotent state

def swapMatrix : Mat2 := !![0, 1; 1, 0]

theorem swapMatrix_swaps :
    leftProjection * swapMatrix = swapMatrix * complementIdempotent leftProjection := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [leftProjection, swapMatrix, complementIdempotent,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem swapMatrix_square : swapMatrix * swapMatrix = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

example (momentum : ℝ) :
    (momentum • grading leftProjection + swapMatrix) *
        (momentum • grading leftProjection + swapMatrix) =
      algebraMap ℝ Mat2 (momentum ^ 2 + 1 ^ 2) := by
  apply hamiltonian_square leftProjection swapMatrix momentum 1
    leftProjection_idempotent swapMatrix_swaps
  simpa using swapMatrix_square

example : (1 : Mat2) * swapMatrix + swapMatrix * 1 ≠ 0 := by
  intro anticommutes
  have entry := congrArg (fun matrix : Mat2 => matrix 0 1) anticommutes
  norm_num [swapMatrix] at entry

example : leftProjection * (1 : Mat2) = (1 : Mat2) * leftProjection := by simp

example (scores : Mat2) : leftProjection * softmaxAttention scores * leftProjection ≠ 0 :=
  softmaxAttention_not_off_diagonal scores

example : softmaxAttention 0 * softmaxAttention 0 ≠ (4 : ℝ) • (1 : Mat2) :=
  zero_scores_square_not_scalar 4

#print axioms exists_unique_decomposition
#print axioms range_kernel_orthogonal_of_symmetric
#print axioms grading_anticommutes
#print axioms signed_momentum_square
#print axioms hamiltonian_square
#print axioms softmaxAttention_not_swap
#print axioms zero_scores_square_not_scalar
#print axioms ProjectionCouplingDependencies.no_cycle

end InfoGeometry.QuantumContext.ProjectionCouplingTests
