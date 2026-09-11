import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option linter.unusedSectionVars false

open Matrix
open scoped BigOperators

namespace NormalizedTracePositivity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Normalized trace operator for real n × n matrices with scale factor d -/
noncomputable def normalizedTrace (d : ℝ) (M : Matrix n n ℝ) : ℝ :=
  (1 / d) * trace M

/-- Lemma: The trace of Aᵀ * A is non-negative (sum of squares of matrix entries) -/
theorem trace_transpose_mul_self_nonneg (A : Matrix n n ℝ) :
    0 ≤ trace (A.transpose * A) := by
  dsimp [trace]
  apply Finset.sum_nonneg
  intro i _
  dsimp [mul_apply, transpose]
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg (A j i)

/-- 🏆 THEOREM: Positivity of the Normalized Trace τ_d(Aᵀ * A) ≥ 0
    Proves that τ_d(Aᵀ * A) ≥ 0 for any real matrix A and dimension factor d > 0. -/
theorem normalizedTrace_positivity (d : ℝ) (hd : 0 < d) (A : Matrix n n ℝ) :
    0 ≤ normalizedTrace d (A.transpose * A) := by
  dsimp [normalizedTrace]
  have h_inv_pos : 0 ≤ 1 / d := div_nonneg zero_le_one (le_of_lt hd)
  have h_tr_pos : 0 ≤ trace (A.transpose * A) := trace_transpose_mul_self_nonneg A
  exact mul_nonneg h_inv_pos h_tr_pos

end NormalizedTracePositivity
