/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryMatrices
import InfoGeometry.OperatorAlgebra.LieJordanOctet

/-!
# Full real matrix specialization and signed-action obstruction

The two coefficients in the countermodel are a non-diagonal square-zero matrix
and its transpose. Their commutator is nonzero. The signed sandwich is not a
positive map, even for this adjoint-paired choice; the symmetric action has the
separate positivity theorem in `LieJordanBoundaryMatrices`.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices

open Matrix
open scoped Matrix
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanOctet

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_trace_oriented (u v x : Matrix n n ℝ) :
    Matrix.trace (orientedTransport (R := ℝ) u v x) =
      -Matrix.trace ((u * v - v * u) * x) :=
  trace_orientedTransport (R := ℝ) (Matrix.traceAddMonoidHom n ℝ)
    Matrix.trace_mul_comm u v x

/-- A genuinely non-diagonal coefficient on the full real matrix algebra. -/
def jump : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, -1]

def jumpAdjoint : Matrix (Fin 2) (Fin 2) ℝ := jumpᴴ

theorem jump_square_zero : jump * jump = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jump, Matrix.mul_apply, Fin.sum_univ_succ]

theorem jump_noncommutes_adjoint : jump * jumpAdjoint ≠ jumpAdjoint * jump := by
  intro h
  have h01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 1) h
  norm_num [jumpAdjoint, jump, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ] at h01

/-- The image of the positive identity already fails positivity. -/
theorem oriented_adjoint_not_positive :
    ¬(orientedTransport (R := ℝ) jump jumpᴴ 1).PosSemidef := by
  intro h
  have ht := h.dotProduct_mulVec_nonneg ![1, 1]
  norm_num [orientedTransport_apply, jump, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Matrix.mulVec,
    Matrix.vecMul, Matrix.transpose_apply, Fin.sum_univ_succ] at ht

end InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices
