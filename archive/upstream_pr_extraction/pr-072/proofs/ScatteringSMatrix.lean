import Mathlib
import proofs.BraidCliffordIntegration

/-!
# Scattering S-Matrix from Clifford Braid Words

Extracts the finite scattering matrix associated to a braid word in the local
`BraidIntegration` namespace.  The current Clifford representation is uniform,
so Artin invariance follows from the already-proved local Artin relations.

The module also records the phase-corrected gate `i · twoAtomParity`, whose
cubic closure is `G³ = -G`, matching the anti-Hermitian/projective convention.
-/

noncomputable section

open Matrix Complex
open InfoGeometry.GrandUnification.BraidIntegration

namespace InfoGeometry.GrandUnification.Scattering

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Phase-corrected local braid generator.  If `P = twoAtomParity` and `P²=I`, then
`(iP)²=-I` and `(iP)³=-(iP)`. -/
def phaseBraidGate (_i : ℕ) : M2C :=
  Complex.I • twoAtomParity

/-- The phase-corrected gate has square `-I`. -/
theorem phaseBraidGate_sq (i : ℕ) :
    phaseBraidGate i * phaseBraidGate i = -(1 : M2C) := by
  rw [phaseBraidGate]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [twoAtomParity, sigma3, iSigma2]

/-- The phase-corrected gate satisfies `G³ = -G`. -/
theorem phaseBraidGate_cubed_neg (i : ℕ) :
    phaseBraidGate i * phaseBraidGate i * phaseBraidGate i = - phaseBraidGate i := by
  calc
    phaseBraidGate i * phaseBraidGate i * phaseBraidGate i
        = (phaseBraidGate i * phaseBraidGate i) * phaseBraidGate i := by simp [mul_assoc]
    _ = (-(1 : M2C)) * phaseBraidGate i := by rw [phaseBraidGate_sq]
    _ = - phaseBraidGate i := by simp

/-- Scattering matrix associated to a finite braid word: ordered product of local gates. -/
def scatteringSMatrix {n : ℕ} : BraidWord n → M2C
  | [] => 1
  | i :: ws => cliffordBraidGate i.val * scatteringSMatrix ws

/-- Phase-corrected version of the scattering matrix. -/
def phaseScatteringSMatrix {n : ℕ} : BraidWord n → M2C
  | [] => 1
  | i :: ws => phaseBraidGate i.val * phaseScatteringSMatrix ws

/-- The local scattering matrix is invariant under finite Artin moves. -/
theorem s_matrix_is_topologically_invariant
    {n : ℕ} {w1 w2 : BraidWord n} (h_move : ArtinMove w1 w2) :
    scatteringSMatrix w1 = scatteringSMatrix w2 := by
  induction h_move with
  | adjacent i h =>
      dsimp [scatteringSMatrix]
      simpa [mul_assoc] using clifford_adjacent_artin i.val
  | separated i j h =>
      dsimp [scatteringSMatrix]
      simpa [mul_assoc] using clifford_separated_artin i.val j.val h
  | trans w1 w2 w3 h1 h2 ih1 ih2 =>
      exact ih1.trans ih2

/-- Phase-corrected scattering is also invariant under finite Artin moves in the current
uniform local representation. -/
theorem phase_s_matrix_is_topologically_invariant
    {n : ℕ} {w1 w2 : BraidWord n} (h_move : ArtinMove w1 w2) :
    phaseScatteringSMatrix w1 = phaseScatteringSMatrix w2 := by
  induction h_move with
  | adjacent i h =>
      dsimp [phaseScatteringSMatrix, phaseBraidGate]
  | separated i j h =>
      dsimp [phaseScatteringSMatrix, phaseBraidGate]
  | trans w1 w2 w3 h1 h2 ih1 ih2 =>
      exact ih1.trans ih2

/-- S-matrix after successor-stage embedding agrees on Artin-equivalent words. -/
theorem embedded_s_matrix_is_topologically_invariant
    {n : ℕ} {w1 w2 : BraidWord n} (h_move : ArtinMove w1 w2) :
    scatteringSMatrix (finiteToInfinite w1) =
      scatteringSMatrix (finiteToInfinite w2) := by
  induction h_move with
  | adjacent i h =>
      dsimp [finiteToInfinite, scatteringSMatrix]
      simpa [mul_assoc] using clifford_adjacent_artin i.val
  | separated i j h =>
      dsimp [finiteToInfinite, scatteringSMatrix]
      simpa [mul_assoc] using clifford_separated_artin i.val j.val h
  | trans w1 w2 w3 h1 h2 ih1 ih2 =>
      exact ih1.trans ih2

/-- Consolidated scattering package. -/
theorem scattering_smatrix_synthesis :
    (∀ i : ℕ, phaseBraidGate i * phaseBraidGate i = -(1 : M2C)) ∧
    (∀ i : ℕ, phaseBraidGate i * phaseBraidGate i * phaseBraidGate i = - phaseBraidGate i) ∧
    (∀ n : ℕ, ∀ w1 w2 : BraidWord n,
      ArtinMove w1 w2 → scatteringSMatrix w1 = scatteringSMatrix w2) ∧
    (∀ n : ℕ, ∀ w1 w2 : BraidWord n,
      ArtinMove w1 w2 → phaseScatteringSMatrix w1 = phaseScatteringSMatrix w2) ∧
    (∀ n : ℕ, ∀ w1 w2 : BraidWord n,
      ArtinMove w1 w2 →
        scatteringSMatrix (finiteToInfinite w1) = scatteringSMatrix (finiteToInfinite w2)) := by
  exact ⟨phaseBraidGate_sq, phaseBraidGate_cubed_neg,
    fun _ _ _ h => s_matrix_is_topologically_invariant h,
    fun _ _ _ h => phase_s_matrix_is_topologically_invariant h,
    fun _ _ _ h => embedded_s_matrix_is_topologically_invariant h⟩

end InfoGeometry.GrandUnification.Scattering
