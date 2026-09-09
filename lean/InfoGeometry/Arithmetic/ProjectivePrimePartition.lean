/-
InfoGeometry/Arithmetic/ProjectivePrimePartition.lean

Witness-gated modular flow of von Mangoldt weights over the projective
temperature interval.

This module is a narrow facade over `PrimitivePrimeProjectiveTemperature`.
It gives the compact-flow name `projectivePrimePartition` and a model
calibration socket, without asserting analytic continuation, the prime number
theorem, an Euler product, or the logarithmic-derivative theorem for `ζ`.
-/

import InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

noncomputable section

namespace InfoGeometry.Arithmetic.ProjectivePrimePartition

open InfoGeometry.Arithmetic
open InfoGeometry.Thermodynamics.ProjectiveTemperature
open InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

/-! ## 1. Projective von Mangoldt partition flow -/

/--
Projected von Mangoldt partition evaluated at inverted temperature `u = 1 / β`.

This is the finite-support compact-temperature shadow of the prime-weighted
Dirichlet readout.  It is not an analytic assertion about `-ζ'/ζ`.
-/
def projectivePrimePartition (A : Finset ℕ) (u : ℝ) : ℝ :=
  arithmeticPrimePartition A (betaInvert u)

/-- The projective prime partition is the restricted prime partition at `β = u⁻¹`. -/
theorem projectivePrimePartition_eq_restricted
    (A : Finset ℕ) (u : ℝ) :
    projectivePrimePartition A u =
      arithmeticPrimeRestrictedPartition A (betaInvert u) :=
  rfl

/-- The projective prime partition is nonnegative. -/
theorem projectivePrimePartition_nonneg
    (A : Finset ℕ) (u : ℝ) :
    0 ≤ projectivePrimePartition A u := by
  simpa [projectivePrimePartition] using
    arithmeticPrimePartition_nonneg A (betaInvert u)

/-- The projective prime partition is positive on supports containing a positive-weight state. -/
lemma projectivePrimePartition_pos_of_mem_positive_weight
    {A : Finset ℕ} {u : ℝ} {n : ℕ}
    (hnA : n ∈ A) (hΛ : 0 < realVonMangoldt n) (hn : 1 < n) :
    0 < projectivePrimePartition A u := by
  exact arithmeticPrimeRestrictedPartition_pos_of_mem_positive_weight
    (β := betaInvert u) hnA hΛ hn

/--
On the compact interval `(0, 1)`, the inverted temperature lies in the
ordinary low-temperature regime `β > 1`.
-/
theorem one_lt_projective_beta_of_mem_Ioo
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    1 < betaInvert u :=
  one_lt_betaInvert_of_mem_Ioo_zero_one hu

/-! ## 2. Model calibration socket -/

/--
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

/-- The calibrated modular flow readout is positive on supports containing a positive-weight state. -/
lemma modularFlowReadout_pos_of_mem_positive_weight
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) {n : ℕ}
    (hnA : n ∈ A) (hΛ : 0 < realVonMangoldt n) (hn : 1 < n) :
    0 < C.modularFlowReadout (C.stateOfFinset A) u := by
  rw [C.flow_eq_projectivePrimePartition A u hu]
  exact projectivePrimePartition_pos_of_mem_positive_weight hnA hΛ hn

end ProjectivePrimeCalibration

end InfoGeometry.Arithmetic.ProjectivePrimePartition

