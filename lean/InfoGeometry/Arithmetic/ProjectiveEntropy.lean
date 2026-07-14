/-
InfoGeometry/Arithmetic/ProjectiveEntropy.lean

Witness-gated comparison between the primitive-weight projective density and
the von Mangoldt / prime-weighted projective density.

This module does not prove a KL-divergence theorem, Jensen inequality, prime
number theorem, or analytic zeta estimate.  It packages finite-support
projective density comparison data and re-exports the consequences supplied by
that witness.
-/

import InfoGeometry.Thermodynamics.ProjectiveTemperature
import InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

noncomputable section

namespace ProjectiveEntropy

open InfoGeometry.Thermodynamics.ProjectiveTemperature
open InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

/-! ## 1. Relative density comparison socket -/

/--
Witness comparing the primitive projective density with the finite von
Mangoldt / prime-weighted projective density over the compact temperature
interval `(0, 1)`.

The relative readout is deliberately model-supplied.  This file only requires
that it is calibrated to the two finite densities and optionally nonnegative.
-/
structure RelativeEntropyWitness
    (A : Finset ℕ) where
  /-- Model-specific relative entropy/divergence/readout between the two lanes. -/
  relativeReadout : ℝ → ℝ

  /--
  Calibration law: the readout is a model-supplied comparison of primitive
  density and prime/von-Mangoldt density at compact temperature `u`.
  -/
  relative_eq_density_difference :
    ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      relativeReadout u =
        primitiveInvertedPartitionDensity A u -
          arithmeticPrimeInvertedPartitionDensity A u

  /--
  Optional positivity certificate for the supplied relative readout.

  This is a witness field rather than a theorem about all finite supports.
  -/
  relative_nonneg :
    ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      0 ≤ relativeReadout u

namespace RelativeEntropyWitness

variable {A : Finset ℕ}
variable (W : RelativeEntropyWitness A)

/-- Re-export the supplied density-comparison calibration law. -/
theorem readout_eq_density_difference
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    W.relativeReadout u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u :=
  W.relative_eq_density_difference u hu

/-- Re-export the supplied nonnegativity law. -/
theorem readout_nonneg
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ W.relativeReadout u :=
  W.relative_nonneg u hu

/--
A nonnegative relative readout gives the corresponding pointwise density
comparison on the compact projective interval.
-/
theorem prime_density_le_primitive_density
    (W : RelativeEntropyWitness A)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
      primitiveInvertedPartitionDensity A u := by
  have hnonneg := RelativeEntropyWitness.readout_nonneg W hu
  rw [RelativeEntropyWitness.readout_eq_density_difference W hu] at hnonneg
  linarith

end RelativeEntropyWitness

/-! ## 2. State-space calibration socket -/

/--
A geometric/thermodynamic state-space calibration for the relative projective
entropy between primitive and prime projective densities.
-/
structure ProjectiveRelativeEntropyCalibration
    (State : Type*) where
  /-- Encode a finite arithmetic support as a model state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific relative readout on compact projective temperature. -/
  relativeReadout : State → ℝ → ℝ

  /-- Supplied finite-support relative entropy witness for each encoded support. -/
  witnessOfFinset :
    ∀ A : Finset ℕ, RelativeEntropyWitness A

  /-- The state readout agrees with the supplied finite witness. -/
  readout_eq_law :
    ∀ A : Finset ℕ, ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      relativeReadout (stateOfFinset A) u =
        (witnessOfFinset A).relativeReadout u

namespace ProjectiveRelativeEntropyCalibration

variable {State : Type*}
variable (C : ProjectiveRelativeEntropyCalibration State)

/-- Calibrated state readout as a primitive-minus-prime density difference. -/
theorem readout_eq_density_difference
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    C.relativeReadout (C.stateOfFinset A) u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u := by
  rw [C.readout_eq_law A u hu]
  exact (C.witnessOfFinset A).readout_eq_density_difference hu

/-- The calibrated relative readout is nonnegative when supplied by the witness. -/
theorem readout_nonneg
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ C.relativeReadout (C.stateOfFinset A) u := by
  rw [C.readout_eq_law A u hu]
  exact (C.witnessOfFinset A).readout_nonneg hu

/-- Calibrated nonnegativity gives pointwise prime-density domination. -/
theorem prime_density_le_primitive_density
    (C : ProjectiveRelativeEntropyCalibration State)
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
      primitiveInvertedPartitionDensity A u :=
  RelativeEntropyWitness.prime_density_le_primitive_density
    (ProjectiveRelativeEntropyCalibration.witnessOfFinset C A) hu

end ProjectiveRelativeEntropyCalibration

end ProjectiveEntropy
