/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.BostConnesKMSPhaseTransition

/-!
# Finite matrix Gibbs/KMS stage for the Bost--Connes weight model

This owner deliberately stops at a finite matrix stage.  It supplies a
trace-normalized Gibbs functional and the temperature predicates, but makes
no claim about an infinite trace, analytic continuation, or KMS-state
classification.
-/

namespace InfoGeometry.Canonical.BostConnesFiniteMatrixKMS

noncomputable section

open Matrix
open InfoGeometry.Algebra.BostConnesKMSPhaseTransition

abbrev Carrier (N : ℕ) := Matrix (Fin N) (Fin N) ℝ

def partition (w : Fin N → ℝ) : ℝ := ∑ i, w i

def gibbsDensity (w : Fin N → ℝ) : Carrier N :=
  Matrix.diagonal (fun i => (partition w)⁻¹ * w i)

def gibbsFunctional (w : Fin N → ℝ)
    (A : Carrier N) : ℝ :=
  Matrix.trace (gibbsDensity w * A)

theorem gibbsFunctional_one (w : Fin N → ℝ) (hZ : partition w ≠ 0) :
    gibbsFunctional w (1 : Carrier N) = 1 := by
  unfold gibbsFunctional gibbsDensity
  rw [mul_one, Matrix.trace_diagonal]
  dsimp [partition]
  rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ hZ

def lowTemperature (β : ℝ) : Prop := 1 < β

def phaseBoundary (β : ℝ) : Prop := 0 < β ∧ β ≤ 1

theorem lowTemperature_implies_not_phaseBoundary (β : ℝ)
    (hβ : lowTemperature β) : ¬ phaseBoundary β := by
  dsimp [lowTemperature, phaseBoundary] at *
  intro h
  linarith

theorem phaseBoundary_or_lowTemperature (β : ℝ) (hβ : 0 < β) :
    phaseBoundary β ∨ lowTemperature β := by
  dsimp [phaseBoundary, lowTemperature]
  by_cases h : β ≤ 1
  · exact Or.inl ⟨hβ, h⟩
  · exact Or.inr (lt_of_not_ge h)

theorem normalized_gibbs_stage (β : ℝ) (hβ : 1 < β)
    (w : Fin N → ℝ) (hZ : partition w ≠ 0) :
    gibbsFunctional w (1 : Carrier N) = 1 ∧
      ¬ phaseBoundary β := by
  exact ⟨gibbsFunctional_one w hZ, lowTemperature_implies_not_phaseBoundary β hβ⟩

end

end InfoGeometry.Canonical.BostConnesFiniteMatrixKMS
