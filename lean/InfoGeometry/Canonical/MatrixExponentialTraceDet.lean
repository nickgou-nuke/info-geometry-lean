import InfoGeometry.Canonical.ModularWeldBridge
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Matrix exponential trace-determinant problem packet

This file does two things:

* it records the missing global analytic theorem as an explicit Lean problem
  surface;
* it gives the fully proved diagonal shadow by a stepwise lemma chain.

The global identity

`Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`

is still not available as a general owner theorem in the current repo/mathlib
stack, so the general statement is packaged as data rather than asserted as a
proven theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixExponentialTraceDet

open scoped Matrix
open scoped BigOperators

/-- The missing analytic owner statement, packaged as an explicit proposition. -/
def detExpEqExpTrace {n : ℕ} (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (A : Matrix (Fin n) (Fin n) R) : Prop :=
  Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)

/--
Problem packet for the matrix exponential trace-determinant law.

This records the intended owner theorem together with the analytic premises and
the repo-native diagonal shadow. It does not claim the general theorem is
already proved.
-/
structure MatrixExponentialTraceDetProblem
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] where
  /-- Matrix size. -/
  n : ℕ
  /-- Matrix under study. -/
  A : Matrix (Fin n) (Fin n) R
  /-- Determinant multiplicativity premise. -/
  det_mul_premise : Prop
  /-- Exponential differential-equation premise. -/
  exp_ode_premise : Prop
  /-- Trace cyclicity premise. -/
  trace_cyclicity_premise : Prop
  /-- Determinant derivative at the identity premise. -/
  det_derivative_premise : Prop
  /-- The owner target statement. -/
  target : detExpEqExpTrace (R := R) A

section DiagonalShadow

variable {n : ℕ}

/-- First explicit step: the matrix exponential of a diagonal matrix is diagonal. -/
lemma exp_diagonal_step (v : Fin n → ℝ) :
    NormedSpace.exp (Matrix.diagonal v) = Matrix.diagonal (NormedSpace.exp v) := by
  simpa using (Matrix.exp_diagonal (v := v))

/-- Second explicit step: the determinant of a diagonal matrix is the product of its diagonal. -/
lemma det_diagonal_step (v : Fin n → ℝ) :
    Matrix.det (Matrix.diagonal (NormedSpace.exp v)) = ∏ i, Real.exp (v i) := by
  have hfun : NormedSpace.exp v = fun i => Real.exp (v i) := by
    funext i
    simp [Real.exp_eq_exp_ℝ]
  rw [hfun]
  simpa using (Matrix.det_diagonal (d := fun i => Real.exp (v i)))

/-- Third explicit step: the trace of a diagonal matrix is the sum of its diagonal. -/
lemma trace_diagonal_step (v : Fin n → ℝ) :
    Matrix.trace (Matrix.diagonal v) = ∑ i, v i := by
  rw [Matrix.trace_diagonal]

/-- Fourth explicit step: the exponential of the trace of a diagonal matrix is the product of
its diagonal exponentials. -/
lemma exp_trace_diagonal_step (v : Fin n → ℝ) :
    NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) = ∏ i, Real.exp (v i) := by
  rw [trace_diagonal_step]
  simpa [Real.exp_eq_exp_ℝ] using (Real.exp_sum (s := Finset.univ) (f := v))

/--
The diagonal trace-determinant law for the matrix exponential, proved by the
explicit rewrite chain:

* `Matrix.exp_diagonal`
* `Matrix.det_diagonal`
* `Matrix.trace_diagonal`
* `Real.exp_sum`
-/
theorem det_exp_diagonal_eq_exp_trace_explicit (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [exp_diagonal_step]
  rw [det_diagonal_step]
  rw [exp_trace_diagonal_step]

/-- Repo-native diagonal shadow of the missing global theorem. -/
theorem det_exp_diagonal_eq_exp_trace_shadow (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace_explicit v

/-- Diagonal packet re-export for downstream consumers. -/
theorem packet_det_exp_diagonal_eq_exp_trace (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace_shadow v

end DiagonalShadow

end InfoGeometry.Canonical.MatrixExponentialTraceDet
