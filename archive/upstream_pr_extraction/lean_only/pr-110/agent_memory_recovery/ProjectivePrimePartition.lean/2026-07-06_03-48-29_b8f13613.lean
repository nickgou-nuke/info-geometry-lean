Calibration socket for a physical/geometric state space whose internal modular
flow readout reproduces the finite projective von Mangoldt partition on
`u ∈ (0, 1)`.
-/
structure ProjectivePrimeCalibration (State : Type*) where
  /-- Map a finite arithmetic support to the geometric state. -/
  stateOfFinset : Finset ℕ → State

  /-- Endogenous modular generator/flow readout on the state. -/
  modularFlowReadout : State → ℝ → ℝ

  /-- Calibration law on the compact projective temperature interval. -/
  flow_eq_projectivePrimePartition :
    ∀ A : Finset ℕ, ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      modularFlowReadout (stateOfFinset A) u = projectivePrimePartition A u

namespace ProjectivePrimeCalibration

variable {State : Type*}
variable (C : ProjectivePrimeCalibration State)

/-- The modular flow readout matches the arithmetic prime partition at `β = 1 / u`. -/
theorem flowReadout_eq_arithmeticPrimePartition
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    C.modularFlowReadout (C.stateOfFinset A) u =
      arithmeticPrimePartition A (betaInvert u) := by
  rw [C.flow_eq_projectivePrimePartition A u hu]
  rfl

/-- The calibrated modular flow readout is nonnegative on finite supports. -/
theorem modularFlowReadout_nonneg
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ C.modularFlowReadout (C.stateOfFinset A) u := by
  rw [C.flow_eq_projectivePrimePartition A u hu]
  exact projectivePrimePartition_nonneg A u

end ProjectivePrimeCalibration

end InfoGeometry.Arithmetic.ProjectivePrimePartition

