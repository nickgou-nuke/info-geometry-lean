import Mathlib.Data.Real.Basic

namespace Omega.Discussion

/-- A finite decoupling witness yields simulator and HSZK bounds by monotonicity of the error
scales. -/
theorem paper_discussion_2design_decoupling_hszk
    (macroSectorCount : ℕ)
    (decouplingError simulatorError hszkTolerance simulatorReference : ℝ)
    (macroSectorSimulator : Fin macroSectorCount → ℝ)
    (decouplingWitness :
      ∀ i : Fin macroSectorCount,
        |macroSectorSimulator i - simulatorReference| ≤ decouplingError)
    (decouplingToSimulator : decouplingError ≤ simulatorError)
    (simulatorToHSZK : simulatorError ≤ hszkTolerance) :
    (∀ i : Fin macroSectorCount,
        |macroSectorSimulator i - simulatorReference| ≤ decouplingError) ∧
      (∃ simulator : Fin macroSectorCount → ℝ,
        ∀ i : Fin macroSectorCount,
          |simulator i - simulatorReference| ≤ simulatorError) ∧
      (∃ simulator : Fin macroSectorCount → ℝ,
        ∀ i : Fin macroSectorCount,
          |simulator i - simulatorReference| ≤ hszkTolerance) := by
  refine ⟨decouplingWitness, ⟨macroSectorSimulator, ?_⟩,
    ⟨macroSectorSimulator, ?_⟩⟩
  · intro i
    exact le_trans (decouplingWitness i) decouplingToSimulator
  · intro i
    exact le_trans (le_trans (decouplingWitness i) decouplingToSimulator) simulatorToHSZK

end Omega.Discussion
