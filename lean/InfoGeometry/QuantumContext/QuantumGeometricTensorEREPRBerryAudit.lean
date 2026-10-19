/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.QuantumGeometricTensorEREPRBerry

/-!
# Audit: Finite Native Matrix Symmetric–Skew Identities

The integer examples and axiom audit cover the actual `Matrix (Fin 2) (Fin 2) R`
theorems in this module. They do not certify Fisher/Berry geometry, a quantum
geometric tensor, or an ER=EPR correspondence.
-/

open scoped Matrix

namespace InfoGeometry.QuantumContext.FiniteMatrixSymmetricSkewAudit

open InfoGeometry.QuantumContext.FiniteMatrixSymmetricSkew

/-- Concrete symmetric/skew decomposition and Frobenius pairing over `ℤ`. -/
theorem sample_matrix_symmetric_skew_int :
    let Q : Mat2 ℤ := !![3, 5; 1, 4]
    let S := symmetricPartTwice Q
    let A := skewPartTwice Q
    S = !![6, 6; 6, 8] ∧
      A = !![0, 4; -4, 0] ∧
      frobeniusPairing S A = 0 ∧
      frobeniusPairing S S = 172 ∧
      frobeniusPairing A A = 32 ∧
      4 * frobeniusPairing Q Q = 204 ∧
      frobeniusPairing S S + frobeniusPairing A A =
        4 * frobeniusPairing Q Q := by
  decide

/-- Concrete native-matrix off-diagonal square and determinant readback. -/
theorem sample_off_diagonal_matrix_sq_int :
    let W := offDiagonalMatrix (3 : ℤ) 7
    W * W = !![21, 0; 0, 21] ∧
      negativeDeterminant (3 : ℤ) 7 = 21 ∧
      twiceOffDiagonalProduct (3 : ℤ) 7 = 42 := by
  decide

#print axioms symmetricPartTwice_is_symmetric
#print axioms symmetric_add_skew_eq_two_smul
#print axioms symmetric_skew_frobenius_pairing_zero
#print axioms symmetric_skew_pythagorean_frobenius_norm
#print axioms offDiagonalMatrix_sq_diagonal
#print axioms offDiagonalDeterminant_identity
#print axioms offDiagonalMatrix_nilpotent_left_zero
#print axioms sample_matrix_symmetric_skew_int
#print axioms sample_off_diagonal_matrix_sq_int

end InfoGeometry.QuantumContext.FiniteMatrixSymmetricSkewAudit
