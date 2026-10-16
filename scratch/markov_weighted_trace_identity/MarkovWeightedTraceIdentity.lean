/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovFullMatrixGreen

/-!
# Full-matrix weighted pairing as a matrix trace

This scratch candidate states the exact finite-dimensional trace readout of
the existing stationary-weighted pairing. Both arguments remain arbitrary
full matrices; the diagonal matrix is only the weight operator.
-/

open Matrix

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The stationary weights represented as a diagonal operator. -/
def stationaryWeightOperator (π : ι → ℝ) : Matrix ι ι ℝ := Matrix.diag π

/-- The full-matrix weighted Frobenius pairing is the trace pairing against
the stationary weight operator. No restriction is imposed on either matrix.
-/
theorem weightedMatrixPairing_eq_trace_weighted_product
    (π : ι → ℝ) (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π X Y =
      Matrix.trace (stationaryWeightOperator π * X * Yᵀ) := by
  classical
  unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
    stationaryWeightOperator
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_ite_eq']
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- In particular, the finite full-matrix Green form is a trace expression.
This is just the pairing readout applied to an arbitrary group-inverse image.
-/
theorem weightedMatrixPairing_groupInverse_greenForm_eq_trace
    (π : ι → ℝ) (G X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (G * X) =
      Matrix.trace (stationaryWeightOperator π * X * (G * X)ᵀ) :=
  weightedMatrixPairing_eq_trace_weighted_product π X (G * X)

end InfoGeometry.QuantumContext.MarkovDrazin
