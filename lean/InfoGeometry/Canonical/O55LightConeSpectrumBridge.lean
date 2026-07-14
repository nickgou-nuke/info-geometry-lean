import Mathlib

/-!
# O(5,5) Light-Cone Spectrum Bridge

This module formalizes the finite linear-algebra readout of the proposed
`Cl(1,1)^5` doubled coordinate basis:

* the first doubled cell is rotated into light-cone coordinates;
* the remaining eight coordinates are the transverse coordinates;
* the decidable integer core has Gram matrix `diag(2,2,1,...,1)`, so the first
  doubled cell is the only part needing the external `1 / sqrt 2`
  normalization used by the SymPy witness;
* the shifted closed-string mass readout with zero intercept is recorded as a
  conditional algebraic formula.

#### BUCKET 1: CLOSED FINITE THEOREMS
`lightConeIntegerCore_gram`, `doubled_ground_massSq_zero`,
`doubled_first_excited_massSq`, and `intercept_zero_reduces_standard_massSq`
are closed algebraic theorems.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The standard mass formula reduction depends on the explicit premise `intercept = 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove a physical string spectrum, BRST consistency,
Virasoro constraints, modular invariance, an `E₆(₆)` symmetry action, or a
derived cancellation of the intercept from first principles.
-/

noncomputable section

namespace O55LightConeSpectrumBridge

open Matrix

abbrev M10Z := Matrix (Fin 10) (Fin 10) ℤ

/--
The decidable integer core of the finite light-cone projection matrix.

Rows `0,1` perform the unnormalized light-cone rotation of the first doubled
cell. Rows `2` through `9` leave the eight transverse coordinates fixed.  The
SymPy witness applies the external normalization `1 / sqrt 2` to the first
block.
-/
def lightConeIntegerCore : M10Z :=
  !![1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     1, -1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/--
The Gram matrix of the integer light-cone core.  The first two directions have
length square `2`; all transverse directions have length square `1`.
-/
def lightConeGramTarget : M10Z :=
  !![2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Decidable finite Gram check for the `O(5,5)` light-cone integer core. -/
theorem lightConeIntegerCore_gram :
    lightConeIntegerCoreᵀ * lightConeIntegerCore = lightConeGramTarget := by
  native_decide

/-- Standard closed-string mass-square algebraic readout. -/
def standardClosedMassSq (alphaPrime excitation intercept : ℝ) : ℝ :=
  (4 / alphaPrime) * (excitation - intercept)

/-- Doubled-space zero-intercept mass-square algebraic readout. -/
def doubledClosedMassSq (alphaPrime excitation : ℝ) : ℝ :=
  (4 / alphaPrime) * excitation

/-- Setting the intercept to zero reduces the standard formula to the doubled readout. -/
theorem intercept_zero_reduces_standard_massSq
    {alphaPrime excitation intercept : ℝ} (hintercept : intercept = 0) :
    standardClosedMassSq alphaPrime excitation intercept =
      doubledClosedMassSq alphaPrime excitation := by
  simp [standardClosedMassSq, doubledClosedMassSq, hintercept]

/-- The zero-intercept ground-state readout is massless algebraically. -/
theorem doubled_ground_massSq_zero (alphaPrime : ℝ) :
    doubledClosedMassSq alphaPrime 0 = 0 := by
  simp [doubledClosedMassSq]

/-- The first excited zero-intercept readout is `4 / alphaPrime`. -/
theorem doubled_first_excited_massSq (alphaPrime : ℝ) :
    doubledClosedMassSq alphaPrime 1 = 4 / alphaPrime := by
  simp [doubledClosedMassSq]

/-- The finite packet combining the light-cone integer core and zero-intercept readout. -/
theorem lightCone_zeroIntercept_packet (alphaPrime : ℝ) :
    lightConeIntegerCoreᵀ * lightConeIntegerCore = lightConeGramTarget ∧
      doubledClosedMassSq alphaPrime 0 = 0 ∧
      doubledClosedMassSq alphaPrime 1 = 4 / alphaPrime :=
  ⟨lightConeIntegerCore_gram,
    doubled_ground_massSq_zero alphaPrime,
    doubled_first_excited_massSq alphaPrime⟩

end O55LightConeSpectrumBridge
