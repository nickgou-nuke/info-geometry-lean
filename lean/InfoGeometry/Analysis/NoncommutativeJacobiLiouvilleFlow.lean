import InfoGeometry.Analysis.FiniteMatrixJacobiDerivative

noncomputable section

namespace InfoGeometry.Analysis.NoncommutativeJacobiLiouvilleFlow

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Trace-cyclicity for the left-generator conjugate `U⁻¹ * (A * U)`.

This is the noncommutative readout step: the trace collapses the similarity
conjugate to the bare generator without any commuting assumption.
-/
theorem trace_conjugate_left_generator
    (U A : Matrix n n ℝ) (hU : IsUnit U) :
    Matrix.trace (U⁻¹ * (A * U)) = Matrix.trace A := by
  have hdetU : IsUnit U.det :=
    (Matrix.isUnit_iff_isUnit_det U).mp hU
  calc
    Matrix.trace (U⁻¹ * (A * U))
        = Matrix.trace ((U⁻¹ * A) * U) := by
            rw [mul_assoc]
    _ = Matrix.trace ((U * U⁻¹) * A) := by
          exact Matrix.trace_mul_cycle (U⁻¹) A U
    _ = Matrix.trace ((1 : Matrix n n ℝ) * A) := by
          have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdetU
          rw [hmul]
    _ = Matrix.trace A := by simp

/--
Jacobi--Liouville determinant derivative for a noncommutative left-generator
matrix path `U' = A(t) * U(t)`.

No commuting hypothesis is used.  The determinant derivative is reduced to the
generator trace only after the similarity-conjugate trace is collapsed by
cyclicity.
-/
theorem hasDerivAt_det_of_left_generator
    {U A : ℝ → Matrix n n ℝ} {t : ℝ}
    (hU : ∀ i j : n, HasDerivAt (fun u : ℝ => U u i j) ((A t * U t) i j) t)
    (hInv : IsUnit (U t)) :
    HasDerivAt
      (fun u : ℝ => (U u).det)
      ((U t).det * Matrix.trace (A t))
      t := by
  have hdet :=
    InfoGeometry.Analysis.FiniteMatrixJacobiDerivative.hasDerivAt_det_of_hasDerivAt_matrix
      (J := U) (Jdot := A t * U t) (t := t) hU hInv
  have htrace :
      Matrix.trace ((U t)⁻¹ * (A t * U t)) = Matrix.trace (A t) := by
    simpa [mul_assoc] using
      trace_conjugate_left_generator (U := U t) (A := A t) hInv
  simpa [htrace, mul_assoc] using hdet

/--
Determinant flow readout for a noncommutative generator path.

This is the exact operator-level Liouville/Jacobi statement:
the determinant derivative is the determinant times the generator trace.
-/
theorem det_derivative_left_generator
    {U A : ℝ → Matrix n n ℝ} {t : ℝ}
    (hU : ∀ i j : n, HasDerivAt (fun u : ℝ => U u i j) ((A t * U t) i j) t)
    (hInv : IsUnit (U t)) :
    deriv (fun u : ℝ => (U u).det) t =
      (U t).det * Matrix.trace (A t) :=
  (hasDerivAt_det_of_left_generator (U := U) (A := A) (t := t) hU hInv).deriv

end InfoGeometry.Analysis.NoncommutativeJacobiLiouvilleFlow
