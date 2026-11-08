import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete visible-fiber data for the fold-gauge mutual-information bound. The learner law is a
scalar proxy for the conditional law on the hidden state, `visibleSection` picks a representative
from each visible fiber, and the numeric fields record the data-processing comparison together
with the entropy identity `H(X^n) = n * H(π)`. -/
structure FoldGaugeMiBoundData where
  visibleStates : ℕ
  hiddenStates : ℕ
  visible : Fin hiddenStates → Fin visibleStates
  visibleSection : Fin visibleStates → Fin hiddenStates
  learnerLaw : Fin hiddenStates → ℚ
  sampleCount : ℕ
  baseEntropy : ℚ
  learnerMutualInfo : ℚ
  visibleMutualInfo : ℚ

/-- The induced visible random map obtained by evaluating the learner law on the chosen visible
fiber representative. -/
def inducedVisibleLaw (D : FoldGaugeMiBoundData) (v : Fin D.visibleStates) : ℚ :=
  D.learnerLaw (D.visibleSection v)

/-- Scalar proxy for the entropy identity `H(X^n) = n * H(π)`. -/
def foldGaugeSampleEntropy (n : ℕ) (piEntropy : ℚ) : ℚ :=
  (n : ℚ) * piEntropy

/-- Paper label: `prop:op-algebra-fold-gauge-mi-bound`.
Fiberwise transitivity makes the learner law constant on visible fibers, so it factors through
the visible variables; data processing and `H(X^n) = n * H(π)` then yield the information bound.
-/
theorem paper_op_algebra_fold_gauge_mi_bound
    (D : FoldGaugeMiBoundData)
    (visible_section : ∀ v, D.visible (D.visibleSection v) = v)
    (fiberwiseTransitive :
      ∀ x y, D.visible x = D.visible y → D.learnerLaw x = D.learnerLaw y)
    (dataProcessing_h : D.learnerMutualInfo ≤ D.visibleMutualInfo)
    (visibleEntropy_h : D.visibleMutualInfo =
      (D.sampleCount : ℚ) * D.baseEntropy) :
    (∀ x, D.learnerLaw x = inducedVisibleLaw D (D.visible x)) ∧
      D.learnerMutualInfo ≤ foldGaugeSampleEntropy D.sampleCount D.baseEntropy := by
  constructor
  · intro x
    unfold inducedVisibleLaw
    exact fiberwiseTransitive x (D.visibleSection (D.visible x))
      (visible_section _).symm
  · dsimp [foldGaugeSampleEntropy]
    calc
      D.learnerMutualInfo ≤ D.visibleMutualInfo := dataProcessing_h
      _ = (D.sampleCount : ℚ) * D.baseEntropy := visibleEntropy_h

end Omega.OperatorAlgebra
