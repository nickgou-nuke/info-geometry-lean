/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGravity.WittenCrossedProductTypeII

/-!
# Concrete Integer Examples for Section 112: Finite Matrix-Trace Identities
Target: `InfoGeometry/QuantumGravity/WittenCrossedProductTypeIIAudit.lean`

Verifies over `ℤ` (`decide`) the finite matrix-coordinate readout and cyclicity
of the ordinary `2 × 2` matrix trace. This audit does not instantiate a crossed
product or Type II factor.
-/

namespace InfoGeometry.QuantumGravity.WittenCrossedProductAudit

open InfoGeometry.QuantumGravity.WittenCrossedProduct

/-- Concrete verification of `finiteTraceReadout` and `trace_mul_comm` over `ℤ`. -/
theorem sample_finite_matrix_readout_int :
    let W : MatrixHamiltonianData ℤ := ⟨12, 7, 3, -2⟩
    totalOp W = ⟨12, 0, 0, 7⟩ ∧
    finiteTraceReadout W = 19 ∧
    W.H_grav + W.K_mod = 19 := by
  decide

/-- Concrete verification of cyclic trace invariance `Tr(A · B) = Tr(B · A)` on non-commuting matrix-coordinate records. -/
theorem sample_matrix_trace_comm_int :
    let A : MatrixCoord2 ℤ := ⟨2, 3, 1, 4⟩
    let B : MatrixCoord2 ℤ := ⟨5, 1, 2, 3⟩
    MatrixCoord2.mul A B ≠ MatrixCoord2.mul B A ∧
    MatrixCoord2.trace (MatrixCoord2.mul A B) = 29 ∧
    MatrixCoord2.trace (MatrixCoord2.mul B A) = 29 := by
  decide

#print axioms MatrixCoord2.matrixCoord2_mul_noncommutative
#print axioms MatrixCoord2.trace_mul_comm
#print axioms MatrixCoord2.trace_add
#print axioms finiteTraceReadout_eq_parameter_sum
#print axioms sample_finite_matrix_readout_int
#print axioms sample_matrix_trace_comm_int

end InfoGeometry.QuantumGravity.WittenCrossedProductAudit
