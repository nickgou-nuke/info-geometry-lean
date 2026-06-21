-- InfoGeometry/OperatorAlgebra/SL2CTraceIdentity.lean
import Mathlib.LinearAlgebra.Matrix
import Mathlib.LinearAlgebra.FinTwo
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fin.Succ
import Mathlib.Data.Fin.Zeros

open Matrix
open Fin
open FinTwo

namespace InfoGeometry.OperatorAlgebra

/-- SL(2,C) trace identity: For 2x2 matrices A, B over a commutative ring with det A = det B = 1,
    we have tr(A) * tr(B) = tr(A * B) + tr(A * B⁻¹). -/
theorem sl2c_trace_identity {R : Type*} [CommRing R] 
    (A B : Matrix (Fin 2) (Fin 2) R) (hA : A.det = 1) (hB : B.det = 1) :
    A.trace * B.trace = (A * B).trace + (A * B⁻¹).trace := by
  have h₁ : B⁻¹ = !![(B 1 1), -(B 0 1); -(B 1 0), (B 0 0)] := by
    -- Formula for inverse of 2x2 matrix when determinant is 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.inv_eq_right_inv, Matrix.mul_apply, Fin.sum_univ_succ, hA, hB]
    <;>
      (try ring_nf at * <;> simp_all [Matrix.ext_iff, Fin.forall_fin_two, Fin.forall_fin_succ, Fin.forall_fin_zero]) <;>
      (try aesop) <;>
      (try
        {
          rw [Matrix.ext_iff]
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_succ, pow_two, mul_comm, mul_assoc, mul_left_comm]
          <;> ring_nf at * <;> nlinarith
        })
  rw [h₁]
  -- Now compute traces and simplify using determinant condition
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, pow_two, mul_comm, mul_assoc, mul_left_comm, hA, hB]
  <;>
  (try ring_nf at * <;> nlinarith) <;>
  (try
    {
      -- Use the determinant hypotheses to simplify
      have h₂ : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by simpa [Matrix.det_fin_two] using hA
      have h₃ : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by simpa [Matrix.det_fin_two] using hB
      -- Now we need to show the equality; we can use nlinarith after squaring? Actually it's linear in entries.
      nlinarith [sq_nonneg (A 0 0 + A 1 1 - (B 0 0 + B 1 1)),
        sq_nonneg (A 0 0 - A 1 1), sq_nonneg (B 0 0 - B 1 1),
        sq_nonneg (A 0 1 - A 1 0), sq_nonneg (B 0 1 - B 1 0)]
    }) <;>
  (try
    {
      nlinarith [sq_nonneg (A 0 0 + A 1 1 - (B 0 0 + B 1 1)),
        sq_nonneg (A 0 0 - A 1 1), sq_nonneg (B 0 0 - B 1 1),
        sq_nonneg (A 0 1 - A 1 0), sq_nonneg (B 0 1 - B 1 0)]
    })

end InfoGeometry.OperatorAlgebra