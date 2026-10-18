/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.QuantumGeometricTensorEREPRBerry

/-!
# Concrete Integer Instantiation & Audit for Section 119: QGT Symmetric–Skew & Off-Diagonal Identities
Target: `InfoGeometry/QuantumContext/QuantumGeometricTensorEREPRBerryAudit.lean`

Verifies over `ℤ` (`decide`) and via `#print axioms` that `symmetricPartTwice`, `skewPartTwice`,
`frobeniusPairing`, `metricBracket`, and `offDiagonalMatrix` satisfy all Section 119 identities.
-/

namespace InfoGeometry.QuantumContext.QGTBerryEREPRAudit

open InfoGeometry.QuantumContext.QGTBerryEREPR
open InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op

/-- Concrete verification of symmetric–skew Frobenius orthogonality and Pythagorean norm partition over `ℤ`. -/
theorem sample_qgt_symmetric_skew_pythagorean_int :
    let Q : Cl11Op ℤ := ⟨3, 5, 1, 4⟩
    let S := symmetricPartTwice Q
    let A := skewPartTwice Q
    S = ⟨6, 6, 6, 8⟩ ∧
    A = ⟨0, 4, -4, 0⟩ ∧
    frobeniusPairing S A = 0 ∧
    frobeniusPairing S S = 172 ∧
    frobeniusPairing A A = 32 ∧
    4 * frobeniusPairing Q Q = 204 ∧
    frobeniusPairing S S + frobeniusPairing A A = 4 * frobeniusPairing Q Q := by
  decide

/-- Concrete verification of `offDiagonalMatrix_sq_diagonal` and `offDiagonalDeterminant_identity` over `ℤ`. -/
theorem sample_off_diagonal_matrix_sq_int :
    let W := offDiagonalMatrix (3 : ℤ) 7
    mul W W = ⟨21, 0, 0, 21⟩ ∧
    negativeDeterminant (3 : ℤ) 7 = 21 ∧
    twiceOffDiagonalProduct (3 : ℤ) 7 = 42 := by
  decide

#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.canonicalOp_ne_zero
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.mul_noncommutative_int
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.frobeniusPairing_eq_trace_transpose_mul
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.det_mul
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.symmetricPartTwice_is_symmetric
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.symmetric_add_skew_eq_two_smul
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.symmetric_skew_frobenius_pairing_zero
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.symmetric_skew_pythagorean_frobenius_norm
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.metricBracket_indefinite_over_reals
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.metricBracket_not_positiveSemidefinite
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.cross_metric_bracket_hamiltonian_entropy_zero
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.offDiagonalMatrix_sq_diagonal
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.offDiagonalDeterminant_identity
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.Cl11Op.offDiagonalMatrix_nilpotent_left_zero
#print axioms InfoGeometry.QuantumContext.QGTBerryEREPR.finite_matrix_identity_bundle

end InfoGeometry.QuantumContext.QGTBerryEREPRAudit
