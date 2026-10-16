/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovFullMatrixGreen

/-!
# Trace readout of the full-matrix Markov Green pairing

The stationary weights are represented by a diagonal density operator, while
the observables and Green operator remain arbitrary full matrices. This gives
an exact finite-stage trace expression for the existing Markov pairing; it
does not assert a colimit state or an iteration limit.
-/

open Matrix

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Diagonal operator representing the weights in the full-matrix pairing. -/
def weightDiagonalOperator (π : ι → ℝ) : Matrix ι ι ℝ := Matrix.diagonal π

/-- The full-matrix weighted pairing is the trace of the weighted product.
The diagonal matrix records the weights; neither matrix argument is restricted
to a diagonal subalgebra. -/
theorem weightedMatrixPairing_eq_trace_weighted_product
    (π : ι → ℝ) (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π X Y =
      Matrix.trace (weightDiagonalOperator π * X * Yᵀ) := by
  classical
  have htrace :
      Matrix.trace (Matrix.diagonal π * X * Yᵀ) =
        ∑ i, ∑ j, π i * X i j * Y i j := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.diagonal, Matrix.transpose_apply, mul_assoc]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  change weightedMatrixPairing π X Y =
    Matrix.trace (Matrix.diagonal π * X * Yᵀ)
  rw [htrace]
  unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
  rw [Finset.sum_comm]

/-- Applying the pairing trace identity to a right matrix factor gives a
full-matrix trace readout. Callers may specialize that factor to a supplied
group-inverse image. -/
theorem weightedMatrixPairing_rightFactor_eq_trace
    (π : ι → ℝ) (G X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X (G * X) =
      Matrix.trace
        (weightDiagonalOperator π * X * (G * X)ᵀ) := by
  exact weightedMatrixPairing_eq_trace_weighted_product π X (G * X)

end InfoGeometry.QuantumContext.MarkovDrazin
