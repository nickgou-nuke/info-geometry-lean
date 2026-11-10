/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction

/-!
# ThermalTimeMonodromyBridge

A conservative bridge between two existing owner lanes:

1. modular thermal time from `InfoGeometry.Canonical.YangMillsContinuum`, and
2. de Rham winding/monodromy from `InfoGeometry.Projective.KleinQuadricMonodromy`.

This file does not identify `ℝ`-valued modular time with `ℤ`-valued winding by
fiat. Instead it introduces an explicit calibration map from winding labels to
real times and proves compatibility theorems relative to that calibration.

## Cl(1,1) data boundary

The imported Cl(1,1) construction supplies a square-zero operator and its
commutator residue. This file also records that witness, but does not map it to
the Hilbert-space modular flow. The thermal-time/winding relation is conditional
on the explicit calibration supplied here; identifying it with the Cl(1,1)
residue remains an open bridge requiring an intertwiner and compatibility proof.
-/

namespace InfoGeometry.Canonical.ThermalTimeMonodromyBridge

open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/--
Calibration data relating an integer winding label to a real modular-time
parameter.
-/
structure ThermalTimeWindingCalibration where
  period : ℝ
  period_ne_zero : period ≠ 0

/-- The real modular-time readout assigned to winding label `n`. -/
def ThermalTimeWindingCalibration.timeOfWinding
    (C : ThermalTimeWindingCalibration) (n : ℤ) : ℝ :=
  (n : ℝ) * C.period

/-- The nonzero-period hypothesis makes the winding-to-time map faithful. -/
theorem timeOfWinding_injective (C : ThermalTimeWindingCalibration) :
    Function.Injective C.timeOfWinding := by
  intro m n h
  apply Int.cast_injective (α := ℝ)
  apply mul_right_cancel₀ C.period_ne_zero
  simpa [ThermalTimeWindingCalibration.timeOfWinding] using h

/-- Zero thermal time occurs exactly at zero winding. -/
theorem timeOfWinding_eq_zero_iff (C : ThermalTimeWindingCalibration) (n : ℤ) :
    C.timeOfWinding n = 0 ↔ n = 0 := by
  constructor
  · intro h
    apply timeOfWinding_injective C
    simpa [ThermalTimeWindingCalibration.timeOfWinding] using h
  · rintro rfl
    simp [ThermalTimeWindingCalibration.timeOfWinding]

/-- One calibration period identifies the unit winding. -/
theorem timeOfWinding_eq_period_iff (C : ThermalTimeWindingCalibration) (n : ℤ) :
    C.timeOfWinding n = C.period ↔ n = 1 := by
  constructor
  · intro h
    apply timeOfWinding_injective C
    simpa [ThermalTimeWindingCalibration.timeOfWinding] using h
  · rintro rfl
    simp [ThermalTimeWindingCalibration.timeOfWinding]

@[simp] theorem timeOfWinding_add (C : ThermalTimeWindingCalibration) (m n : ℤ) :
    C.timeOfWinding (m + n) = C.timeOfWinding m + C.timeOfWinding n := by
  change ((m + n : ℤ) : ℝ) * C.period =
    (m : ℝ) * C.period + (n : ℝ) * C.period
  rw [Int.cast_add, add_mul]

section Bridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Minimal bridge package: modular Radon-Nikodym data together with a winding/time
calibration and a positive circle radius for the de Rham winding theorems.
-/
structure BridgeData where
  modularData : ModularRadonNikodymData E
  calibration : ThermalTimeWindingCalibration
  radius : ℝ
  radius_pos : 0 < radius

/-- The continuously calibrated flow uses the calibration period as its time
scale. Its derivative records how changing the winding-time normalization
rescales the infinitesimal modular generator. -/
noncomputable def calibratedModularFlow
    (B : BridgeData (E := E)) (t : ℝ) (A : EndH E) : EndH E :=
  modularAutomorphismGroup B.modularData (t * B.calibration.period) A

set_option maxHeartbeats 800000
/-- The calibration period scales the infinitesimal modular generator. -/
theorem hasDerivAt_calibratedModularFlow_zero
    (B : BridgeData (E := E)) (A : EndH E) :
    HasDerivAt (fun t : ℝ => calibratedModularFlow B t A)
      (B.calibration.period • commutator B.modularData.modularHamiltonian A) 0 := by
  have htime : HasDerivAt (fun t : ℝ => t * B.calibration.period)
      B.calibration.period 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const B.calibration.period
  have hflow := hasDerivAt_modularAutomorphismGroup_zero_eq_commutator
    (M := B.modularData) (A := A)
  have hflow' : HasDerivAt (fun τ : ℝ => modularAutomorphismGroup B.modularData τ A)
      (commutator B.modularData.modularHamiltonian A)
      (0 * B.calibration.period) := by
    simpa using hflow
  have hcomp := HasDerivAt.scomp (𝕜 := ℝ) (F := EndH E) (𝕜' := ℝ)
    (x := 0) hflow' htime
  simpa [calibratedModularFlow, Function.comp_def] using hcomp
set_option maxHeartbeats 200000

/--
The calibrated clock is additive at the level of modular flow: adding winding
labels adds the corresponding thermal parameters.
-/
theorem modularAutomorphismGroup_timeOfWinding_add
    (B : BridgeData (E := E)) (m n : ℤ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (m + n)) A =
      modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding m)
        (modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding n) A) := by
  rw [timeOfWinding_add]
  exact modularAutomorphismGroup_add (M := B.modularData)
    (B.calibration.timeOfWinding m) (B.calibration.timeOfWinding n) A

/--
The same additive compatibility, expressed through the packaged additive modular
flow attached to the modular Hamiltonian.
-/
theorem additiveModularFlow_timeOfWinding_add
    (B : BridgeData (E := E)) (m n : ℤ) (A : EndH E) :
    B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (m + n)) A =
      B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding m)
        (B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding n) A) := by
  rw [toAdditiveModularFlow_apply, toAdditiveModularFlow_apply,
    toAdditiveModularFlow_apply, timeOfWinding_add]
  exact modularAutomorphismGroup_add (M := B.modularData)
    (B.calibration.timeOfWinding m) (B.calibration.timeOfWinding n) A

/--
The de Rham winding class at label `n` is the standard residue readout
`n · 2πi` on the calibrated bridge radius.
-/
theorem deRhamClass_of_calibrated_winding
    (B : BridgeData (E := E)) (n : ℤ) :
    (n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase n := by
  calc
    (n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)
        = (n : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
            rw [circleIntegral_one_div B.radius B.radius_pos]
    _ = logarithmicPhase n := rfl

/--
The corresponding Wilson-loop phase closes to unit holonomy at every integer
winding label on the calibrated bridge radius.
-/
theorem wilsonPhase_of_calibrated_winding
    (B : BridgeData (E := E)) (n : ℤ) :
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) := by
  rw [circleIntegral_one_div B.radius B.radius_pos]
  exact Complex.exp_int_mul_two_pi_mul_I n

/--
The concrete `Cl(1,1)` carrier residue from
`Cl11MonodromyDictionaryConstruction` supplies an explicit square-zero modular
generator together with a commutator residue operator.

This theorem is intentionally conservative: it records the availability of the
concrete operator-algebraic data, without identifying it with the winding
calibration in this file by fiat.
-/
theorem cl11_concrete_monodromy_data_available :
    ∃ K : InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier,
      K * K = 0 := by
  refine ⟨InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction.modularHamiltonian, ?_⟩
  exact InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction.modularHamiltonian_sq

/--
Unit-period calibration used alongside the concrete Cl(1,1) example.

This definition does not depend on the Cl(1,1) residue operator and does not
identify its commutator action with the Hilbert-space modular flow. It fixes a
normalization of the winding-to-time map; a genuine identification with a
specific residue flow would require an intertwining map and a compatibility
theorem.
-/
def cl11CanonicalCalibration : ThermalTimeWindingCalibration :=
  { period := 1
    period_ne_zero := by norm_num }

/--
Bridge data with the fixed unit-period calibration.

The modular Radon-Nikodym data and reference radius are supplied independently.
The Cl(1,1) square-zero witness above is not an input to this constructor, so
this packages a normalized winding/time bridge but does not identify the
Cl(1,1) residue action with the modular flow. Other period normalizations can
be supplied through `ThermalTimeWindingCalibration` directly.
-/
def cl11BridgeData (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (modularData : ModularRadonNikodymData E) (radius : ℝ) (h_radius : 0 < radius) :
    BridgeData (E := E) where
  modularData := modularData
  calibration := cl11CanonicalCalibration
  radius := radius
  radius_pos := h_radius

/--
Under the unit-period normalization, the calibrated modular-flow parameter for
integer winding `n` is the real number `n`. This is a reparameterization result
for the supplied modular flow; it does not assert that the flow is generated by
the separate Cl(1,1) residue witness.
-/
theorem cl11_calibrated_flow_agrees (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (modularData : ModularRadonNikodymData E) (radius : ℝ) (h_radius : 0 < radius)
    (n : ℤ) (A : EndH E) :
    let B := cl11BridgeData E modularData radius h_radius
    modularAutomorphismGroup modularData (B.calibration.timeOfWinding n) A =
      modularAutomorphismGroup modularData (n : ℝ) A := by
  dsimp [cl11BridgeData, cl11CanonicalCalibration, ThermalTimeWindingCalibration.timeOfWinding]
  rw [mul_one]

/--
Additivity of the unit-period calibrated modular flow.

The flow at winding `m + n` is the composition of the flows at `m` and `n`.
This uses the modular automorphism group law and the unit-period winding
calibration; it does not use the Cl(1,1) residue witness.
-/
theorem cl11_calibrated_clock_additive (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (modularData : ModularRadonNikodymData E) (radius : ℝ) (h_radius : 0 < radius)
    (m n : ℤ) (A : EndH E) :
    let B := cl11BridgeData E modularData radius h_radius
    modularAutomorphismGroup modularData (B.calibration.timeOfWinding (m + n)) A =
      modularAutomorphismGroup modularData (B.calibration.timeOfWinding m)
        (modularAutomorphismGroup modularData (B.calibration.timeOfWinding n) A) := by
  dsimp [cl11BridgeData, cl11CanonicalCalibration]
  exact modularAutomorphismGroup_timeOfWinding_add (B := cl11BridgeData E modularData radius h_radius) m n A

end Bridge

end InfoGeometry.Canonical.ThermalTimeMonodromyBridge
