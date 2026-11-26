/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge

/-!
# Soldering the finite BdG sheet carrier to the doubled Minkowski metric

This module gives an explicit index equivalence between the doubled BdG stage
`Fin 4 ⊕ Fin 4` and the doubled-spacetime carrier `Fin 2 × Fin 4`. It proves
that the block-diagonal metric `diag(η₁,₃, -η₁,₃)` is carried exactly to the
Hadamard-associated metric `𝒦_diag = Z ⊗ η₁,₃`, and that the corresponding
Krein pairing is preserved under this reindexing.

This is a finite-dimensional soldering theorem. It does not assert a continuum
Yang–Mills manifold, Wightman/OS axioms, or a physical spectral mass gap.
-/

namespace InfoGeometry.Canonical.DoubledMinkowskiSheetSoldering

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge

/-- Non-commutativity witness for the doubled sheet/spacetime matrix carrier. -/
theorem sheetSoldering_noncommWitness :
    ∃ A B : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ, A * B ≠ B * A :=
  exists_noncomm_mat2x4_real

/-- Index equivalence: inl particle sheet is sheet 0, inr hole sheet is sheet 1. -/
def sheetToDoubled : (Fin 4 ⊕ Fin 4) ≃ (Fin 2 × Fin 4) where
  toFun := Sum.elim (fun i => (0, i)) (fun i => (1, i))
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv s := by cases s <;> simp
  right_inv p := by
    rcases p with ⟨s, i⟩
    fin_cases s <;> simp

/-- Doubled Minkowski metric on the sum-index BdG carrier. -/
def doubledMinkowskiSum : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks minkowski4 0 0 (-minkowski4)

/-- Reindexing the sum-index metric gives exactly `𝒦_diag = Z ⊗ η₁,₃`. -/
theorem sheetKrein_reindex_doubledMinkowskiDiag :
    Matrix.reindex sheetToDoubled sheetToDoubled doubledMinkowskiSum =
      doubledMinkowskiDiag := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.reindex_apply, sheetToDoubled, doubledMinkowskiSum,
      doubledMinkowskiDiag, zCut2, minkowski4, Matrix.kronecker, Matrix.one_apply] <;>
    fin_cases i <;> fin_cases j <;> norm_num

/-- Krein pairing on the sum-index doubled BdG carrier. -/
def doubledMinkowskiKreinPair (ψ φ : Fin 4 ⊕ Fin 4 → ℝ) : ℝ :=
  dotProduct ψ ((doubledMinkowskiSum).mulVec φ)

/-- The sum-index Krein pairing equals the doubled-spacetime pairing after
soldering the BdG sheets to the two Minkowski sheets. -/
theorem doubledMinkowskiKreinPair_eq_pairing (ψ φ : Fin 4 ⊕ Fin 4 → ℝ) :
    doubledMinkowskiKreinPair ψ φ =
      dotProduct (fun p : Fin 2 × Fin 4 => ψ (sheetToDoubled.symm p))
        (doubledMinkowskiDiag.mulVec
          (fun p : Fin 2 × Fin 4 => φ (sheetToDoubled.symm p))) := by
  rw [← sheetKrein_reindex_doubledMinkowskiDiag]
  simp [doubledMinkowskiKreinPair, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, sheetToDoubled]

end InfoGeometry.Canonical.DoubledMinkowskiSheetSoldering
