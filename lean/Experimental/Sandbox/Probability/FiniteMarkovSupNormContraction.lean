import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Coordinatewise contraction for finite row-stochastic matrices

For a real matrix with nonnegative entries and row sums equal to one, each
coordinate of its action on a bounded vector is bounded by the same bound.
This is the finite-dimensional sup-norm contraction estimate needed before
any mean-ergodic or Cesàro-limit argument.
-/

namespace InfoGeometry.Experimental.Probability.FiniteMarkovSupNorm

open Matrix

/-- A row-stochastic matrix preserves every coordinatewise absolute-value
bound. The hypothesis uses Mathlib's canonical `Matrix.rowStochastic` set. -/
theorem mulVec_abs_le_of_coordinate_bound {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n))
    (M : ℝ) (hx : ∀ j, |x j| ≤ M) (i : Fin n) :
    |P.mulVec x i| ≤ M := by
  have hP_nonneg : ∀ j, 0 ≤ P i j := fun j =>
    Matrix.nonneg_of_mem_rowStochastic hP
  have hP_rowsum : ∑ j, P i j = 1 :=
    Matrix.sum_row_of_mem_rowStochastic hP i
  rw [Matrix.mulVec_apply_eq_sum]
  calc
    |∑ j : Fin n, P i j * x j| ≤
        ∑ j : Fin n, |P i j * x j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, P i j * |x j| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_of_nonneg (hP_nonneg j)]
    _ ≤ ∑ j : Fin n, P i j * M := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hx j) (hP_nonneg j)
    _ = M := by
      rw [← Finset.sum_mul, hP_rowsum, one_mul]

end InfoGeometry.Experimental.Probability.FiniteMarkovSupNorm
