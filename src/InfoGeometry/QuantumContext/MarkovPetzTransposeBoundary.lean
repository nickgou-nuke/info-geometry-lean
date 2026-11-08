/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovObliqueSupportWitness

/-!
# Transpose preservation for idempotent matrix compression

For a full matrix carrier, the algebraic compression `X ↦ E * X * E` preserves
transpose exactly when its idempotent `E` is symmetric. The concrete strictly
positive Markov transition from `MarkovObliqueSupportWitness` has a nonsymmetric
group-inverse range idempotent, so its compression fails this *-compatibility
test. This is an algebraic boundary result; it makes no positivity or channel
claim.
-/

namespace InfoGeometry.QuantumContext.MarkovPetzTransposeBoundary

open InfoGeometry.QuantumContext.PetzMartingale
open InfoGeometry.QuantumContext.MarkovObliqueSupportWitness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Idempotent compression preserves transpose if and only if its support
idempotent is symmetric. The carrier is the full matrix algebra. -/
theorem petzRecovery_transpose_preserving_iff
    (E : Matrix ι ι ℝ) (hE : E * E = E) :
    (∀ X : Matrix ι ι ℝ,
      Matrix.transpose (petzRecovery E X) =
        petzRecovery E (Matrix.transpose X)) ↔
      Matrix.transpose E = E := by
  constructor
  · intro h
    have h_one := h 1
    simpa [petzRecovery, hE] using h_one
  · intro hT X
    change Matrix.transpose (E * X * E) = E * Matrix.transpose X * E
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hT]
    noncomm_ring

/-- The strictly positive two-state Markov example has an oblique range
idempotent, and compression by it does not preserve transpose on the full
matrix algebra. -/
theorem markovPetzCompression_not_transposePreserving :
    ¬ (∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      Matrix.transpose (petzRecovery rangeIdempotent X) =
        petzRecovery rangeIdempotent (Matrix.transpose X)) := by
  have hE : rangeIdempotent * rangeIdempotent = rangeIdempotent := by
    exact markovRangeIdempotent_idempotent transition laplacianGroupInverse
      laplacianGroupInverse_isGroupInverse
  have h_not_symmetric : Matrix.transpose rangeIdempotent ≠ rangeIdempotent := by
    simpa [rangeIdempotent] using rangeIdempotent_not_symmetric
  intro h_preserving
  exact h_not_symmetric
    ((petzRecovery_transpose_preserving_iff rangeIdempotent hE).mp h_preserving)

end InfoGeometry.QuantumContext.MarkovPetzTransposeBoundary
