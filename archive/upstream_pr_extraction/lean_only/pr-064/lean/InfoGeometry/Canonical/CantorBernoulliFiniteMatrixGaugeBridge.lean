import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

/-!
# Finite matrix gauge readout for the binary Cantor tower

The repository already owns the noncommutative matrix tower and its compatible
normalized trace.  This consumer records the exact matrix-unit readout, which
is the finite-dimensional counterpart of the diagonal gauge word kernel.
No C*-completion or infinite-state extension is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeBridge

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

/-- The finite diagonal `ℓ¹` size used for the trace bound below.  This is
    deliberately a finite-stage seminorm, not the operator norm of a C⋆
    completion. -/
def matrixDiagonalL1Norm (n : ℕ) (A : MatrixStage n) : ℝ :=
  ∑ i : Fin (2 ^ n), ‖A i i‖

theorem matrixTraceState_norm_le_diagonalL1Norm
    (n : ℕ) (A : MatrixStage n) :
    ‖matrixTraceState n A‖ ≤
      (1 / (2 ^ n : ℝ)) * matrixDiagonalL1Norm n A := by
  rw [matrixTraceState_apply]
  rw [norm_mul]
  have hsum : ‖Matrix.trace A‖ ≤ matrixDiagonalL1Norm n A := by
    dsimp [Matrix.trace, matrixDiagonalL1Norm]
    exact norm_sum_le _ _
  have hcoeff : ‖(1 / (2 ^ n : ℂ))‖ = (1 / (2 ^ n : ℝ)) := by
    rw [norm_div, norm_one]
    simp [norm_pow]
  rw [hcoeff]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem matrixTraceState_single (n : ℕ) (i j : Fin (2 ^ n)) :
    matrixTraceState n (Matrix.single i j 1) =
      if i = j then (1 / (2 ^ n : ℂ)) else 0 := by
  rw [matrixTraceState_apply]
  by_cases h : i = j
  · subst j
    simp [Matrix.trace, Matrix.single]
  · simp [Matrix.trace, Matrix.single, h, Ne.symm h]

theorem matrixTraceState_single_diag (n : ℕ) (i : Fin (2 ^ n)) :
    matrixTraceState n (Matrix.single i i 1) =
      (1 / (2 ^ n : ℂ)) := by
  simpa only [if_pos rfl] using matrixTraceState_single n i i

theorem matrixTraceState_single_cross {n : ℕ}
    {i j : Fin (2 ^ n)} (hij : i ≠ j) :
    matrixTraceState n (Matrix.single i j 1) = 0 := by
  simpa only [if_neg hij] using matrixTraceState_single n i j

theorem matrixTraceState_single_diag_eq_binary_weight
    (n : ℕ) (i : Fin (2 ^ n)) :
    matrixTraceState n (Matrix.single i i 1) =
      ((1 / 2 : ℂ) ^ n) := by
  rw [matrixTraceState_single_diag]
  rw [one_div, one_div]
  rw [← inv_pow]

theorem traceFunctional_stage_single (n : ℕ) (i j : Fin (2 ^ n)) :
    traceFunctional
        (stageInjection n (Matrix.single i j 1)) =
      if i = j then (1 / (2 ^ n : ℂ)) else 0 := by
  rw [traceFunctional_stage]
  exact matrixTraceState_single n i j

theorem traceFunctional_stage_single_diag (n : ℕ) (i : Fin (2 ^ n)) :
    traceFunctional
        (stageInjection n (Matrix.single i i 1)) =
      ((1 / 2 : ℂ) ^ n) := by
  rw [traceFunctional_stage]
  exact matrixTraceState_single_diag_eq_binary_weight n i

theorem traceFunctional_stage_single_cross {n : ℕ}
    {i j : Fin (2 ^ n)} (hij : i ≠ j) :
    traceFunctional
        (stageInjection n (Matrix.single i j 1)) = 0 := by
  rw [traceFunctional_stage]
  exact matrixTraceState_single_cross hij

theorem realTraceState_stage_single_diag (n : ℕ) (i : Fin (2 ^ n)) :
    realTraceState.eval
        (stageInjection n (Matrix.single i i 1)) =
      ((1 / 2 : ℝ) ^ n) := by
  rw [realTraceState_stage]
  rw [matrixTraceState_single_diag_eq_binary_weight]
  have hcast : ((1 / 2 : ℂ) ^ n) =
      (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  rfl

theorem realTraceState_stage_single_cross {n : ℕ}
    {i j : Fin (2 ^ n)} (hij : i ≠ j) :
    realTraceState.eval
        (stageInjection n (Matrix.single i j 1)) = 0 := by
  rw [realTraceState_stage]
  rw [matrixTraceState_single_cross hij]
  rfl

end InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeBridge
