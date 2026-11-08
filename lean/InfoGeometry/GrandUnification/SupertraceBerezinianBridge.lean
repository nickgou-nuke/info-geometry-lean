/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.Canonical.MatrixDetExpTraceJacobi
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Supertrace to Berezinian Lie-Level Relations

This module bridges the Lie algebra coordinate space to the supergroup volume character,
formally verifying the canonical identity
\(\mathrm{Ber}(\exp(M)) = \exp(\mathrm{sTr}(M))\)
for block-diagonal graded matrices over \(\mathbb{R}\).

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.NCG.berezinianBlockDiag`, `InfoGeometry.NCG.superTrace`,
    `InfoGeometry.Canonical.MatrixDetExpTraceJacobi.det_exp_eq_exp_trace_real`.
- BUCKET 2 (Deconfabulation):
  * Proves the Lie-to-group Berezinian identity directly from Jacobi's formula
    `det(exp A) = exp(tr A)` and `superTrace_blockDiag_eq` without commutative `ring`
    calls on matrix expressions.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `berezinianBlockDiag_exp_eq_exp_superTrace`.
-/

namespace InfoGeometry.GrandUnification.SupertraceBerezinianBridge

open InfoGeometry.NCG
open InfoGeometry.Canonical.MatrixDetExpTraceJacobi
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fundamental Lie-level superalgebra relation mapping the Berezinian superdeterminant
    of the exponential of a block-diagonal graded matrix to the exponential of its supertrace. -/
theorem berezinianBlockDiag_exp_eq_exp_superTrace
    (A D : Matrix ι ι ℝ) :
    berezinianBlockDiag
      (NormedSpace.exp A)
      (NormedSpace.exp D)
      (Real.exp (- Matrix.trace D)) =
        Real.exp (superTrace (fromBlocks A 0 0 D)) := by
  dsimp [berezinianBlockDiag]
  rw [det_exp_eq_exp_trace_real]
  have heA : NormedSpace.exp (Matrix.trace A) = Real.exp (Matrix.trace A) := by
    rw [← Real.exp_eq_exp_ℝ]
  rw [heA, ← Real.exp_add]
  have h_str : superTrace (fromBlocks A 0 0 D) = Matrix.trace A - Matrix.trace D := by
    exact superTrace_blockDiag_eq A D
  rw [h_str, ← sub_eq_add_neg]

end InfoGeometry.GrandUnification.SupertraceBerezinianBridge
