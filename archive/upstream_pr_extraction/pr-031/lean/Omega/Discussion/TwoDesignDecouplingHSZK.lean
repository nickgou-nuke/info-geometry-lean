import Mathlib.Data.Real.Basic

namespace Omega.Discussion

/-- Concrete carrier for the finite macro-sector simulator and its error scales. -/
structure TwoDesignDecouplingHSZKData where
  macroSectorCount : ℕ
  decouplingError : ℝ
  simulatorError : ℝ
  hszkTolerance : ℝ
  macroSectorSimulator : Fin macroSectorCount → ℝ
  simulatorReference : ℝ

/-- A finite decoupling witness yields simulator and HSZK bounds by monotonicity of the error
scales. -/
theorem paper_discussion_2design_decoupling_hszk
    (D : TwoDesignDecouplingHSZKData)
    (decouplingWitness :
      ∀ i : Fin D.macroSectorCount,
        |D.macroSectorSimulator i - D.simulatorReference| ≤ D.decouplingError)
    (decouplingToSimulator : D.decouplingError ≤ D.simulatorError)
    (simulatorToHSZK : D.simulatorError ≤ D.hszkTolerance) :
    (∀ i : Fin D.macroSectorCount,
        |D.macroSectorSimulator i - D.simulatorReference| ≤ D.decouplingError) ∧
      (∃ simulator : Fin D.macroSectorCount → ℝ,
        ∀ i : Fin D.macroSectorCount,
          |simulator i - D.simulatorReference| ≤ D.simulatorError) ∧
      (∃ simulator : Fin D.macroSectorCount → ℝ,
        ∀ i : Fin D.macroSectorCount,
          |simulator i - D.simulatorReference| ≤ D.hszkTolerance) := by
  refine ⟨decouplingWitness, ⟨D.macroSectorSimulator, ?_⟩, ⟨D.macroSectorSimulator, ?_⟩⟩
  · intro i
    exact le_trans (decouplingWitness i) decouplingToSimulator
  · intro i
    exact le_trans (le_trans (decouplingWitness i) decouplingToSimulator) simulatorToHSZK

end Omega.Discussion
