import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Discussion

/-- The binary entropy term appearing in the Alicki--Fannes/Audenaert continuity estimate. -/
noncomputable def binaryEntropy (ε : ℝ) : ℝ :=
  -(ε * Real.log ε + (1 - ε) * Real.log (1 - ε))

/-- Numerical carrier for the HSZK/Holevo comparison. -/
structure HSZKHolevoData where
  epsilon : ℝ
  delta : ℝ
  verifierDim : ℕ
  holevoInformation : ℝ
  traceDistance : ℕ → ℕ → ℝ
  referenceState : ℕ

/-- A common simulator bound and a pairwise Pinsker estimate yield the Holevo, reverse-Pinsker,
and reference-state HSZK readouts. -/
theorem paper_discussion_hszk_holevo
    (D : HSZKHolevoData)
    (commonSimulatorBound :
      D.holevoInformation ≤
        2 * D.epsilon * Real.log (D.verifierDim : ℝ) +
          2 * binaryEntropy D.epsilon)
    (twoPointPinsker :
      ∀ ω ω' : ℕ,
        D.traceDistance ω ω' ≤ Real.sqrt (8 * Real.log 2 * D.delta)) :
    (D.holevoInformation ≤
      2 * D.epsilon * Real.log (D.verifierDim : ℝ) +
        2 * binaryEntropy D.epsilon) ∧
      (∀ ω ω' : ℕ,
        D.traceDistance ω ω' ≤ Real.sqrt (8 * Real.log 2 * D.delta)) ∧
      (∀ ω : ℕ,
        D.traceDistance ω D.referenceState ≤ Real.sqrt (8 * Real.log 2 * D.delta)) := by
  exact ⟨commonSimulatorBound, twoPointPinsker, fun ω => twoPointPinsker ω D.referenceState⟩

end Omega.Discussion
