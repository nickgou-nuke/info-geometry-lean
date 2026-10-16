/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import InfoGeometry.QuantumContext.MarkovPetzTransposeBoundary

/-!
# Positivity boundary for idempotent matrix compression

On the full real matrix algebra, the sandwich `X ↦ E * X * E` preserves
positive semidefiniteness exactly when its idempotent support `E` is symmetric.
The Markov group-inverse range idempotent already in the owner tree is
nonsymmetric, so its compression fails this positivity-preservation property.
This is a statement about positive semidefinite matrices; it does not assert
complete positivity, trace preservation, or a state-dependent Petz recovery
channel.
-/

namespace InfoGeometry.QuantumContext.MarkovPetzPositivityBoundary

open InfoGeometry.QuantumContext.PetzMartingale
open InfoGeometry.QuantumContext.MarkovObliqueSupportWitness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On the full real matrix carrier, an idempotent sandwich preserves positive
semidefiniteness of every positive semidefinite matrix exactly when the
idempotent is symmetric. -/
theorem petzRecovery_posSemidef_preserving_iff
    (E : Matrix ι ι ℝ) (hE : E * E = E) :
    (∀ X : Matrix ι ι ℝ, X.PosSemidef → (petzRecovery E X).PosSemidef) ↔
      Matrix.transpose E = E := by
  constructor
  · intro h
    have h_image : (petzRecovery E 1).PosSemidef :=
      h 1 Matrix.PosSemidef.one
    have h_E_pos : E.PosSemidef := by
      simpa [petzRecovery, hE] using h_image
    exact h_E_pos.1.isSymm.eq
  · intro hT X hX
    have h_map : (E.transpose).map (starRingEnd ℝ) = E := by
      calc
        (E.transpose).map (starRingEnd ℝ) = E.transpose := by
          ext i j
          simp
        _ = E := hT
    have h_congr : (E * X * E).PosSemidef := by
      have h := hX.conjTranspose_mul_mul_same E
      change ((E.transpose).map (starRingEnd ℝ) * X * E).PosSemidef at h
      rw [h_map] at h
      exact h
    change (E * X * E).PosSemidef
    exact h_congr

/-- The strictly positive, noncommutative two-state Markov group-inverse
compression is not positivity-preserving on the full matrix algebra. -/
theorem markovPetzCompression_not_posSemidef_preserving :
    ¬ (∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      X.PosSemidef → (petzRecovery rangeIdempotent X).PosSemidef) := by
  have hE : rangeIdempotent * rangeIdempotent = rangeIdempotent := by
    exact markovRangeIdempotent_idempotent transition laplacianGroupInverse
      laplacianGroupInverse_isGroupInverse
  intro h_preserving
  have h_symm : Matrix.transpose rangeIdempotent = rangeIdempotent :=
    (petzRecovery_posSemidef_preserving_iff rangeIdempotent hE).mp h_preserving
  exact rangeIdempotent_not_symmetric h_symm

end InfoGeometry.QuantumContext.MarkovPetzPositivityBoundary
