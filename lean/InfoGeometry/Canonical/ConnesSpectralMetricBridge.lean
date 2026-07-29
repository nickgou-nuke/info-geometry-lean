import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

namespace ConnesSpectralMetricBridge

/-- Connes Spectral Triple (A, H, D) Data Bundle. -/
structure SpectralTripleData where
  commutatorNorm : ℝ → ℝ
  is_nonneg : ∀ a, 0 ≤ commutatorNorm a

/-- Connes Lipschitz Unit Ball: elements a with ||[D, a]|| ≤ 1. -/
def inLipschitzBall (S : SpectralTripleData) (a : ℝ) : Prop :=
  S.commutatorNorm a ≤ 1

/-- Connes Spectral Distance for two state evaluation functions ϕ and ψ over a test element a. -/
def spectralDistanceEval (phi psi : ℝ → ℝ) (a : ℝ) : ℝ :=
  |phi a - psi a|

/-- **Theorem**: Connes Spectral Distance Evaluation Symmetry:
    |ϕ(a) - ψ(a)| = |ψ(a) - ϕ(a)|. -/
theorem spectral_distance_eval_symm (phi psi : ℝ → ℝ) (a : ℝ) :
    spectralDistanceEval phi psi a = spectralDistanceEval psi phi a := by
  dsimp [spectralDistanceEval]
  rw [abs_sub_comm]

/-- **Theorem**: Connes Spectral Distance Evaluation Non-Negativity:
    |ϕ(a) - ψ(a)| ≥ 0. -/
theorem spectral_distance_eval_nonneg (phi psi : ℝ → ℝ) (a : ℝ) :
    0 ≤ spectralDistanceEval phi psi a :=
  abs_nonneg (phi a - psi a)

/-- **Theorem**: Connes Spectral Distance Evaluation Triangle Inequality:
    |ϕ(a) - η(a)| ≤ |ϕ(a) - ψ(a)| + |ψ(a) - η(a)|. -/
theorem spectral_distance_eval_triangle (phi psi eta : ℝ → ℝ) (a : ℝ) :
    spectralDistanceEval phi eta a ≤
    spectralDistanceEval phi psi a + spectralDistanceEval psi eta a := by
  dsimp [spectralDistanceEval]
  have h := abs_sub_le (phi a) (psi a) (eta a)
  exact h

end ConnesSpectralMetricBridge
