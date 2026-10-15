import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Experimental.Sandbox.Probability.FiniteMarkovSupNormContraction

/-!
# Uniform coordinate bounds for iterates of finite Markov matrices

Inductively propagate a coordinatewise absolute-value bound through every
natural power of a finite row-stochastic matrix. No convergence assertion is
made here.
-/

namespace InfoGeometry.Experimental.Probability.FiniteMarkovSupNorm

open Matrix

/-- Every natural iterate of a finite row-stochastic matrix preserves any
coordinatewise absolute-value bound on its input. -/
theorem pow_mulVec_abs_le_of_coordinate_bound {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n)) (M : ℝ) :
    ∀ k (x : Fin n → ℝ), (∀ j, |x j| ≤ M) →
      ∀ i, |(P ^ k).mulVec x i| ≤ M := by
  intro k
  induction k with
  | zero =>
      intro x hx i
      simpa only [pow_zero, Matrix.one_mulVec] using hx i
  | succ k ih =>
      intro x hx i
      rw [pow_succ' P k, ← Matrix.mulVec_mulVec]
      exact mulVec_abs_le_of_coordinate_bound P _ hP M (ih x hx) i

end InfoGeometry.Experimental.Probability.FiniteMarkovSupNorm
