/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CyclicQuotient
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Compression-defined trace need not be cyclic

This refutes only X ↦ Tr(P X P) on the ambient algebra. Ordinary full matrix
trace still exists and extends the trace of this rank-two corner.
-/

namespace InfoGeometry.Algebra.CornerCompressionTraceCounterexample

abbrev Mat3Z := Matrix (Fin 3) (Fin 3) ℤ

def projector : Mat3Z := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def enterCorner : Mat3Z := !![0, 0, 1; 0, 0, 0; 0, 0, 0]
def leaveCorner : Mat3Z := !![0, 0, 0; 0, 0, 0; 1, 0, 0]

theorem projector_idempotent : projector * projector = projector := by decide

theorem projector_not_central : projector * enterCorner ≠ enterCorner * projector := by
  decide

theorem compressed_commutator_trace :
    Matrix.trace (projector * (enterCorner * leaveCorner - leaveCorner * enterCorner) *
      projector) = 1 := by decide

theorem compressed_products_trace_ne :
    Matrix.trace (projector * (enterCorner * leaveCorner) * projector) ≠
      Matrix.trace (projector * (leaveCorner * enterCorner) * projector) := by decide

theorem compression_not_cyclic :
    ¬ ∀ X Y : Mat3Z, Matrix.trace (projector * (X * Y) * projector) =
      Matrix.trace (projector * (Y * X) * projector) := by
  intro h
  exact compressed_products_trace_ne (h enterCorner leaveCorner)

/-- The compression functional cannot descend to the additive cyclic quotient. -/
theorem compression_no_cyclic_factor :
    ¬ ∃ f : CyclicQuotient.CyclicModule ℤ Mat3Z →ₗ[ℤ] ℤ,
      ∀ X : Mat3Z, f (CyclicQuotient.cyclicClass ℤ Mat3Z X) =
        Matrix.trace (projector * X * projector) := by
  rintro ⟨f, hf⟩
  apply compressed_products_trace_ne
  exact (hf _).symm.trans ((congrArg f
    (CyclicQuotient.cyclicClass_mul_comm ℤ Mat3Z enterCorner leaveCorner)).trans (hf _))

end InfoGeometry.Algebra.CornerCompressionTraceCounterexample
