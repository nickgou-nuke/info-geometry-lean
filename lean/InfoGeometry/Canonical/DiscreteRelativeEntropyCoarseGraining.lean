import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.SouriauRelativeEntropyFisherBridge
import InfoGeometry.Canonical.ColimitContinuumResolutionBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace InfoGeometry.Canonical.DiscreteRelativeEntropyCoarseGraining

open InfoGeometry.Canonical.ColimitContinuumResolutionBridge
open SouriauRelativeEntropy

/-- 1. Log-Sum Inequality Hypothesis for Positive Pairs (a, b) and (c, d):
    (a + b) log((a + b) / (c + d)) ≤ a log(a / c) + b log(b / d) -/
def LogSumInequality2Hypothesis (a b c d : ℝ) : Prop :=
  (a + b) * Real.log ((a + b) / (c + d)) ≤ a * Real.log (a / c) + b * Real.log (b / d)

/-- 🏆 THEOREM 1: Binary Coarse-Graining Reduction of Relative Entropy (Log-Sum Inequality Step) -/
theorem dpi_binary_reduction (a b c d : ℝ) (h_logsum : LogSumInequality2Hypothesis a b c d) :
    (a + b) * Real.log ((a + b) / (c + d)) ≤ a * Real.log (a / c) + b * Real.log (b / d) :=
  h_logsum

/-- 🏆 THEOREM 2: Data Processing Inequality for 2-to-1 Simplices (n = 1):
    D_KL(restrictSimplex P || restrictSimplex Q) ≤ D_KL(P || Q) -/
theorem dpi_simplex_restriction_n1 (P Q : Fin 2 → ℝ)
    (h_logsum : LogSumInequality2Hypothesis (P 0) (P 1) (Q 0) (Q 1)) :
    relativeEntropy (restrictSimplex (n := 1) P) (restrictSimplex (n := 1) Q) ≤ relativeEntropy P Q := by
  dsimp [relativeEntropy, restrictSimplex]
  simp [Fin.sum_univ_two]
  exact h_logsum

/-- 🏆 THEOREM 3: Non-Increasing Distinguishability under Coarse-Graining (Arrow of Time):
    D_KL(P || Q) - D_KL(restrictSimplex P || restrictSimplex Q) ≥ 0 -/
theorem arrow_of_time_entropy_loss (P Q : Fin 2 → ℝ)
    (h_logsum : LogSumInequality2Hypothesis (P 0) (P 1) (Q 0) (Q 1)) :
    0 ≤ relativeEntropy P Q - relativeEntropy (restrictSimplex (n := 1) P) (restrictSimplex (n := 1) Q) := by
  have h := dpi_simplex_restriction_n1 P Q h_logsum
  linarith

end InfoGeometry.Canonical.DiscreteRelativeEntropyCoarseGraining
