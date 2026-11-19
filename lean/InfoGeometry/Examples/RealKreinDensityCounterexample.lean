/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.BdGChiralBlockMatrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum

/-!
# A real Krein-self-adjoint matrix with a real logarithm but no positivity

The metric is the existing `chiralGrading = diag(1,-1)`. The actual real
matrix `candidateDensity = 1 + nilpotentGenerator` has trace two and
determinant one and is self-adjoint for this metric. Its second diagonal
entry and its quadratic value at the second basis vector are negative, so
it is not positive semidefinite in Mathlib's ordinary matrix sense.

Its real logarithm is nevertheless explicit: the actual analytic matrix
exponential of `nilpotentGenerator` equals `candidateDensity`. This is not
merely the finite algebraic operation `IsNilpotent.exp`, and no logarithm
function or spectral functional calculus is silently presumed.
-/

namespace InfoGeometry.Examples.RealKreinDensityCounterexample

open Matrix InfoGeometry.Physics

/-- For a square-zero real matrix the actual exponential series terminates.
This applies in every finite dimension and does not choose a matrix norm. -/
theorem realMatrix_exp_of_sq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (hN : N * N = 0) :
    NormedSpace.exp N = 1 + N := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' k : ℕ, ((Nat.factorial k : ℕ) : ℝ)⁻¹ • N ^ k) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, pow_zero, pow_one]
  · intro k hk
    have hk' : ¬ k < 2 := by simpa only [Finset.mem_range] using hk
    have htwo : 2 ≤ k := Nat.not_lt.mp hk'
    have hpow : N ^ 2 = 0 := by simpa only [pow_two] using hN
    rw [pow_eq_zero_of_le htwo hpow, smul_zero]

/-- A nonzero square-zero matrix self-adjoint for the split form. -/
def nilpotentGenerator : BdGBlock ℝ := !![2, 2; -2, -2]

/-- A proposed density with positive trace and determinant. -/
def candidateDensity : BdGBlock ℝ := 1 + nilpotentGenerator

theorem nilpotentGenerator_sq_zero :
    nilpotentGenerator * nilpotentGenerator = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentGenerator, Matrix.mul_apply, Fin.sum_univ_two]

theorem nilpotentGenerator_ne_zero : nilpotentGenerator ≠ 0 := by
  intro h
  have h00 := congrArg (fun A : BdGBlock ℝ => A 0 0) h
  norm_num [nilpotentGenerator] at h00

/-- This is the native metric self-adjointness predicate, not ordinary
matrix symmetry or a new bespoke adjoint. -/
theorem candidateDensity_krein_selfAdjoint :
    (chiralGrading : BdGBlock ℝ).IsSelfAdjoint candidateDensity := by
  change candidateDensityᵀ * chiralGrading = chiralGrading * candidateDensity
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [candidateDensity, nilpotentGenerator, chiralGrading,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem candidateDensity_trace_det :
    candidateDensity.trace = 2 ∧ candidateDensity.det = 1 := by
  constructor
  · norm_num [candidateDensity, nilpotentGenerator, Matrix.trace,
      Fin.sum_univ_two]
  · norm_num [candidateDensity, nilpotentGenerator, Matrix.det_fin_two]

/-- Positive trace and determinant do not prevent a negative quadratic value. -/
theorem candidateDensity_negative_quadratic :
    candidateDensity.toBilin' ![0, 1] ![0, 1] = -1 := by
  norm_num [candidateDensity, nilpotentGenerator, Matrix.toBilin'_apply',
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The failure is expressed using Mathlib's positive-semidefinite predicate. -/
theorem candidateDensity_not_posSemidef : ¬ candidateDensity.PosSemidef := by
  intro h
  have hdiag : (0 : ℝ) ≤ candidateDensity 1 1 := h.diag_nonneg
  norm_num [candidateDensity, nilpotentGenerator] at hdiag

/-- Nonpositivity does not obstruct existence of a real matrix logarithm:
the nonzero square-zero generator is an explicit logarithm. -/
theorem exp_nilpotentGenerator :
    NormedSpace.exp nilpotentGenerator = candidateDensity :=
  realMatrix_exp_of_sq_zero nilpotentGenerator nilpotentGenerator_sq_zero

end InfoGeometry.Examples.RealKreinDensityCounterexample
