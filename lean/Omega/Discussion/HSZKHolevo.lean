import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Discussion

/-- The binary entropy term appearing in the Alicki--Fannes/Audenaert continuity estimate. -/
noncomputable def binaryEntropy (ε : ℝ) : ℝ :=
  -(ε * Real.log ε + (1 - ε) * Real.log (1 - ε))

/-- A common simulator bound and a pairwise Pinsker estimate yield the Holevo, reverse-Pinsker,
and reference-state HSZK readouts. -/
theorem paper_discussion_hszk_holevo
    (epsilon delta : ℝ) (verifierDim : ℕ) (holevoInformation : ℝ)
    (traceDistance : ℕ → ℕ → ℝ) (referenceState : ℕ)
    (commonSimulatorBound :
      holevoInformation ≤
        2 * epsilon * Real.log (verifierDim : ℝ) + 2 * binaryEntropy epsilon)
    (twoPointPinsker :
      ∀ ω ω' : ℕ,
        traceDistance ω ω' ≤ Real.sqrt (8 * Real.log 2 * delta)) :
    (holevoInformation ≤
      2 * epsilon * Real.log (verifierDim : ℝ) + 2 * binaryEntropy epsilon) ∧
      (∀ ω ω' : ℕ,
        traceDistance ω ω' ≤ Real.sqrt (8 * Real.log 2 * delta)) ∧
      (∀ ω : ℕ,
        traceDistance ω referenceState ≤ Real.sqrt (8 * Real.log 2 * delta)) := by
  exact ⟨commonSimulatorBound, twoPointPinsker,
    fun ω => twoPointPinsker ω referenceState⟩

end Omega.Discussion
