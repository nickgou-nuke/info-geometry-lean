/-
InfoGeometry/Arithmetic/ProjectiveEntropy.lean

Explicit comparison between the primitive-weight projective density and the
von Mangoldt / prime-weighted projective density.

The projective entropy is the repository's native generalized KL divergence
on canonical simplex representatives of finite positive-measure rays. Its
nonnegativity comes from the proved finite log-sum inequality. No prime number
theorem or analytic zeta estimate is asserted. A separate scalar lemma records
the order consequence of an explicitly supplied density calibration.
-/

import InfoGeometry.Thermodynamics.ProjectiveTemperature
import InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature
import InfoGeometry.Projective.ConeKL

noncomputable section

namespace InfoGeometry.Arithmetic.ProjectiveEntropy

open InfoGeometry.Thermodynamics.ProjectiveTemperature
open PrimitivePrimeProjectiveTemperature

/--
Relative entropy of two finite projective positive measures, evaluated on
their canonical simplex representatives.
-/
noncomputable def projectiveRelativeEntropy
    {α : Type*} [Fintype α] [Nonempty α]
    (p q : InfoGeometry.PositiveMeasure.Proj (α := α)) : ℝ :=
  InfoGeometry.Projective.generalizedKLOnProj (α := α) p q

/-- Projective relative entropy is nonnegative by the finite log-sum theorem. -/
theorem projectiveRelativeEntropy_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (p q : InfoGeometry.PositiveMeasure.Proj (α := α)) :
    0 ≤ projectiveRelativeEntropy p q :=
  InfoGeometry.Projective.generalizedKLOnProj_nonneg p q

/--
On representatives, projective relative entropy is generalized KL after
canonical normalization to the simplex.
-/
@[simp]
theorem projectiveRelativeEntropy_mk
    {α : Type*} [Fintype α] [Nonempty α]
    (μ ν : InfoGeometry.PositiveMeasure α ℝ) :
    projectiveRelativeEntropy
        (Quotient.mk _ μ) (Quotient.mk _ ν) =
      InfoGeometry.PositiveMeasure.generalizedKL
        (InfoGeometry.PositiveMeasure.normalize μ)
        (InfoGeometry.PositiveMeasure.normalize ν) :=
  InfoGeometry.Projective.generalizedKLOnProj_mk μ ν

/--
Canonical finite density gap between the primitive and von-Mangoldt
projective-temperature lanes.

This is a density comparison, not a KL divergence.
-/
def projectiveDensityGap (A : Finset ℕ) (u : ℝ) : ℝ :=
  primitiveInvertedPartitionDensity A u -
    arithmeticPrimeInvertedPartitionDensity A u

@[simp]
theorem projectiveDensityGap_eq (A : Finset ℕ) (u : ℝ) :
    projectiveDensityGap A u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u :=
  rfl

/-- Nonnegativity of the canonical gap is exactly pointwise density order. -/
theorem projectiveDensityGap_nonneg_iff (A : Finset ℕ) (u : ℝ) :
    0 ≤ projectiveDensityGap A u ↔
      arithmeticPrimeInvertedPartitionDensity A u ≤
        primitiveInvertedPartitionDensity A u := by
  exact sub_nonneg

/-- A calibrated nonnegative difference orders its two real terms. -/
theorem le_of_readout_eq_sub_of_nonneg
    {readout primitive prime : ℝ}
    (hcalibration : readout = primitive - prime)
    (hnonneg : 0 ≤ readout) :
    prime ≤ primitive := by
  rw [hcalibration] at hnonneg
  exact sub_nonneg.mp hnonneg

/--
An explicitly calibrated nonnegative readout gives the corresponding
pointwise comparison of the two finite projective densities.
-/
theorem prime_density_le_primitive_density
    (A : Finset ℕ) (u readout : ℝ)
    (hcalibration :
      readout =
        primitiveInvertedPartitionDensity A u -
          arithmeticPrimeInvertedPartitionDensity A u)
    (hnonneg : 0 ≤ readout) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
      primitiveInvertedPartitionDensity A u :=
  le_of_readout_eq_sub_of_nonneg hcalibration hnonneg

/-- Canonical-gap formulation of the finite density comparison. -/
theorem prime_density_le_primitive_density_iff_gap_nonneg
    (A : Finset ℕ) (u : ℝ) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
        primitiveInvertedPartitionDensity A u ↔
      0 ≤ projectiveDensityGap A u :=
  (projectiveDensityGap_nonneg_iff A u).symm

/-- Pointwise nonnegativity of the canonical projective density gap.

This restores the historical witness name as the mathematical proposition
itself, rather than as a record containing an arbitrary readout and two
evidence fields.
-/
abbrev RelativeEntropyWitness (A : Finset ℕ) : Prop :=
  ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ projectiveDensityGap A u

namespace RelativeEntropyWitness

/-- Direct theorem for the canonical density-gap readout. -/
theorem canonical_readout_eq_density_difference (A : Finset ℕ) (u : ℝ) :
    projectiveDensityGap A u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u :=
  projectiveDensityGap_eq A u

/-- Direct nonnegativity theorem for the canonical density-gap readout. -/
theorem canonical_readout_nonneg
    (A : Finset ℕ) (u : ℝ)
    (h :
      arithmeticPrimeInvertedPartitionDensity A u ≤
        primitiveInvertedPartitionDensity A u) :
    0 ≤ projectiveDensityGap A u :=
  (projectiveDensityGap_nonneg_iff A u).2 h

/-- Direct order consequence for the canonical density-gap readout. -/
theorem canonical_prime_density_le_primitive_density
    (A : Finset ℕ) (u : ℝ)
    (h : 0 ≤ projectiveDensityGap A u) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
      primitiveInvertedPartitionDensity A u :=
  (projectiveDensityGap_nonneg_iff A u).1 h

variable {A : Finset ℕ}
variable (W : RelativeEntropyWitness A)

/-- Canonical readout attached to the gap-nonnegativity proposition. -/
def relativeReadout (W : RelativeEntropyWitness A) (u : ℝ) : ℝ :=
  projectiveDensityGap A u

/-- The canonical readout is the primitive-minus-prime density difference. -/
theorem readout_eq_density_difference
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    W.relativeReadout u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u :=
  projectiveDensityGap_eq A u

/-- Readback of the gap-nonnegativity proposition. -/
theorem readout_nonneg
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ W.relativeReadout u :=
  W u hu

/-!
The historical calibration record exposed these two laws as fields named
`relative_eq_density_difference` and `relative_nonneg`.  The current owner
derives them from the canonical density-gap readout instead of accepting
model-supplied evidence.  Keep the old theorem names as compatibility
projections, with the canonical owner as their proof source.
-/

@[deprecated readout_eq_density_difference (since := "2026-07-27")]
theorem relative_eq_density_difference
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    W.relativeReadout u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u :=
  W.readout_eq_density_difference hu

@[deprecated readout_nonneg (since := "2026-07-27")]
theorem relative_nonneg
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ W.relativeReadout u :=
  W.readout_nonneg hu

/-- A calibrated nonnegative readout orders the two projective densities. -/
theorem prime_density_le_primitive_density
    (W : RelativeEntropyWitness A)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
      primitiveInvertedPartitionDensity A u := by
  exact le_of_readout_eq_sub_of_nonneg
    (W.readout_eq_density_difference hu) (W.readout_nonneg hu)

end RelativeEntropyWitness

/-- Injective state encoding of finite arithmetic supports.

Unlike the historical calibration record, this native owner stores no
model-supplied readout, calibration equation, or positivity evidence.  It also
does not require every ambient state to be an arithmetic support.
-/
abbrev ProjectiveRelativeEntropyCalibration (State : Type*) :=
  Finset ℕ ↪ State

namespace ProjectiveRelativeEntropyCalibration

/--
An explicitly calibrated state readout equals the canonical finite density
difference.
-/
theorem canonical_readout_eq_density_difference
    {State : Type*}
    (stateOfFinset : Finset ℕ → State)
    (relativeReadout : State → ℝ → ℝ)
    (A : Finset ℕ) (u : ℝ)
    (hcalibration :
      relativeReadout (stateOfFinset A) u = projectiveDensityGap A u) :
    relativeReadout (stateOfFinset A) u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u := by
  rw [hcalibration]
  exact projectiveDensityGap_eq A u

/-- A calibrated state readout is nonnegative when the canonical gap is. -/
theorem canonical_readout_nonneg
    {State : Type*}
    (stateOfFinset : Finset ℕ → State)
    (relativeReadout : State → ℝ → ℝ)
    (A : Finset ℕ) (u : ℝ)
    (hcalibration :
      relativeReadout (stateOfFinset A) u = projectiveDensityGap A u)
    (hgap : 0 ≤ projectiveDensityGap A u) :
    0 ≤ relativeReadout (stateOfFinset A) u := by
  rw [hcalibration]
  exact hgap

/-- Explicit state calibration and nonnegativity imply density domination. -/
theorem canonical_prime_density_le_primitive_density
    {State : Type*}
    (stateOfFinset : Finset ℕ → State)
    (relativeReadout : State → ℝ → ℝ)
    (A : Finset ℕ) (u : ℝ)
    (hcalibration :
      relativeReadout (stateOfFinset A) u = projectiveDensityGap A u)
    (hnonneg : 0 ≤ relativeReadout (stateOfFinset A) u) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
      primitiveInvertedPartitionDensity A u := by
  apply (projectiveDensityGap_nonneg_iff A u).1
  rw [← hcalibration]
  exact hnonneg

variable {State : Type*}
variable (C : ProjectiveRelativeEntropyCalibration State)

/-- The image of the support embedding is the calibrated state space. -/
abbrev CalibratedState
    (C : ProjectiveRelativeEntropyCalibration State) :=
  Set.range C

/-- Encode a finite support as a state in the calibrated image. -/
def stateOfFinset
    (C : ProjectiveRelativeEntropyCalibration State)
    (A : Finset ℕ) : C.CalibratedState :=
  ⟨C A, ⟨A, rfl⟩⟩

/-- Recover the unique finite support represented by a calibrated state. -/
noncomputable def supportOfState
    (C : ProjectiveRelativeEntropyCalibration State)
    (s : C.CalibratedState) : Finset ℕ :=
  Classical.choose s.property

/-- The recovered support maps to the underlying ambient state. -/
theorem supportOfState_spec
    (C : ProjectiveRelativeEntropyCalibration State)
    (s : C.CalibratedState) :
    C (C.supportOfState s) = s.1 :=
  Classical.choose_spec s.property

/-- Recover the canonical density-gap readout from a calibrated state. -/
noncomputable def relativeReadout
    (C : ProjectiveRelativeEntropyCalibration State)
    (s : C.CalibratedState) (u : ℝ) : ℝ :=
  projectiveDensityGap (C.supportOfState s) u

/-- The encoded support is recovered exactly. -/
@[simp]
theorem stateOfFinset_decode
    (C : ProjectiveRelativeEntropyCalibration State)
    (A : Finset ℕ) :
    C.supportOfState (C.stateOfFinset A) = A := by
  apply C.injective
  exact C.supportOfState_spec (C.stateOfFinset A)

/-- The state readout is definitionally the canonical support gap. -/
@[simp]
theorem readout_eq_law
    (C : ProjectiveRelativeEntropyCalibration State)
    (A : Finset ℕ) (u : ℝ) :
    C.relativeReadout (C.stateOfFinset A) u =
      projectiveDensityGap A u := by
  simp [relativeReadout]

/-- Calibrated state readout as a primitive-minus-prime density difference. -/
theorem readout_eq_density_difference
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    C.relativeReadout (C.stateOfFinset A) u =
      primitiveInvertedPartitionDensity A u -
        arithmeticPrimeInvertedPartitionDensity A u := by
  rw [C.readout_eq_law A u]
  exact projectiveDensityGap_eq A u

/-- The calibrated state readout inherits canonical gap nonnegativity. -/
theorem readout_nonneg
    (A : Finset ℕ) {u : ℝ} (_hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hgap : 0 ≤ projectiveDensityGap A u) :
    0 ≤ C.relativeReadout (C.stateOfFinset A) u := by
  rw [C.readout_eq_law A u]
  exact hgap

/-- Canonical gap nonnegativity gives pointwise prime-density domination. -/
theorem prime_density_le_primitive_density
    (C : ProjectiveRelativeEntropyCalibration State)
    (A : Finset ℕ) {u : ℝ} (_hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hgap : 0 ≤ projectiveDensityGap A u) :
    arithmeticPrimeInvertedPartitionDensity A u ≤
      primitiveInvertedPartitionDensity A u :=
  (projectiveDensityGap_nonneg_iff A u).1 hgap

end ProjectiveRelativeEntropyCalibration

end InfoGeometry.Arithmetic.ProjectiveEntropy
