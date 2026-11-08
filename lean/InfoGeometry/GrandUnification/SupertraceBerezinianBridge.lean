import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.Canonical.MatrixDetExpTraceJacobi
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.unusedSectionVars false

/-!
# Supertrace to Berezinian Lie-Level Relations

This module bridges the Lie algebra coordinate space to the supergroup volume character,
formally verifying the canonical identity:
\(\mathrm{Ber}(\exp(M)) = \exp(\mathrm{sTr}(M))\)
for block-diagonal graded matrices over \(\mathbb{R}\).
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
  rw [h_str]
  have h_sub : Matrix.trace A + -Matrix.trace D = Matrix.trace A - Matrix.trace D := by ring
  rw [h_sub]

end InfoGeometry.GrandUnification.SupertraceBerezinianBridge
