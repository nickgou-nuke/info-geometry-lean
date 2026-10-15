import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import InfoGeometry.Canonical.SinkhornFoundation
import Experimental.Sandbox.Probability.FiniteMarkovPowerBound

/-!
# Finite algebraic prerequisites for Markov Cesàro convergence

This file proves the telescoping identity for the image of `1 - P` and the
uniform endpoint estimate used in a later coordinatewise Cesàro limit proof.
It does not assert a convergence result for ordinary powers.
-/

namespace InfoGeometry.Experimental.Probability.FiniteMarkovCesaro

open Matrix

/-- Applying `1 - P` and summing its successive images under powers of `P`
leaves only the two endpoints of the finite orbit. -/
theorem telescoping_one_sub_matrix_mulVec {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (P ^ k).mulVec ((1 - P).mulVec u)) =
      u - (P ^ (N + 1)).mulVec u := by
  have hterm (k : ℕ) :
      (P ^ k).mulVec ((1 - P).mulVec u) =
        (P ^ k).mulVec u - (P ^ (k + 1)).mulVec u := by
    calc
      (P ^ k).mulVec ((1 - P).mulVec u) =
          (P ^ k).mulVec (u - P.mulVec u) := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = (P ^ k).mulVec u - (P ^ k).mulVec (P.mulVec u) := by
          rw [Matrix.mulVec_sub]
      _ = (P ^ k).mulVec u - (P ^ (k + 1)).mulVec u := by
          rw [Matrix.mulVec_mulVec, ← pow_succ]
  calc
    (∑ k ∈ Finset.range (N + 1), (P ^ k).mulVec ((1 - P).mulVec u)) =
        ∑ k ∈ Finset.range (N + 1),
          ((P ^ k).mulVec u - (P ^ (k + 1)).mulVec u) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hterm k
    _ = (P ^ 0).mulVec u - (P ^ (N + 1)).mulVec u := by
          exact InfoGeometry.Canonical.MoE.sum_range_sub_telescope
            (fun k => (P ^ k).mulVec u) (N + 1)
    _ = u - (P ^ (N + 1)).mulVec u := by simp

/-- A row-stochastic matrix cannot move a vector outside its coordinatewise
absolute bound. Consequently, the endpoint difference between the original
vector and any iterate is bounded by twice that bound. -/
theorem endpoint_error_le_two_mul_bound {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n))
    (u : Fin n → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (N : ℕ) (i : Fin n) :
    |u i - (P ^ (N + 1)).mulVec u i| ≤ 2 * M := by
  have hiterate :=
    InfoGeometry.Experimental.Probability.FiniteMarkovSupNorm.pow_mulVec_abs_le_of_coordinate_bound
      P hP M (N + 1) u hu i
  have htriangle := abs_sub_le (u i) 0 ((P ^ (N + 1)).mulVec u i)
  have hleft : |u i - 0| ≤ M := by simpa using hu i
  have hright : |0 - (P ^ (N + 1)).mulVec u i| ≤ M := by
    simpa using hiterate
  calc
    |u i - (P ^ (N + 1)).mulVec u i| ≤
        |u i - 0| + |0 - (P ^ (N + 1)).mulVec u i| := htriangle
    _ ≤ M + M := add_le_add hleft hright
    _ = 2 * M := by ring

end InfoGeometry.Experimental.Probability.FiniteMarkovCesaro
