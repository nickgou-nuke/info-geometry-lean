import InfoGeometry.Canonical.YangMillsContinuum
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

## Connection to Cl(1,1) Monodromy Dictionary

This bridge is compatible with the concrete Cl(1,1) construction in
`InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction`, which provides:

- A square-zero modular Hamiltonian `K` (Witt creation operator)
- A carrier residue operator `Res(X) = [K, X]`
- An explicit characterization of when `Res² = 0` (parabolicity condition)

The calibration data in this file can be instantiated using the Cl(1,1) tower
by choosing the period to match the natural scaling of the Witt generator.
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

@[simp] theorem timeOfWinding_zero (C : ThermalTimeWindingCalibration) :
    C.timeOfWinding 0 = 0 := by
  simp [ThermalTimeWindingCalibration.timeOfWinding]

@[simp] theorem timeOfWinding_one (C : ThermalTimeWindingCalibration) :
    C.timeOfWinding 1 = C.period := by
  simp [ThermalTimeWindingCalibration.timeOfWinding]

@[simp] theorem timeOfWinding_add (C : ThermalTimeWindingCalibration) (m n : ℤ) :
    C.timeOfWinding (m + n) = C.timeOfWinding m + C.timeOfWinding n := by
  simp [ThermalTimeWindingCalibration.timeOfWinding, add_mul]

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

/--
If a chosen thermal parameter `τ` is calibrated to the winding label `n`, then
modular evolution at `τ` agrees with modular evolution at the calibrated time.
-/
theorem modularAutomorphismGroup_eq_calibrated_time
    (B : BridgeData (E := E)) {τ : ℝ} (n : ℤ)
    (hτ : τ = B.calibration.timeOfWinding n) (A : EndH E) :
    modularAutomorphismGroup B.modularData τ A =
      modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding n) A := by
  exact modularAutomorphismGroup_eq_of_time_eq (M := B.modularData) hτ A

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
  exact modularAutomorphismGroup_timeOfWinding_add (B := B) m n A

/--
The de Rham winding class at label `n` is the standard residue readout
`n · 2πi` on the calibrated bridge radius.
-/
theorem deRhamClass_of_calibrated_winding
    (B : BridgeData (E := E)) (n : ℤ) :
    (n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase n := by
  exact deRhamClass_of_winding (R := B.radius) B.radius_pos n

/--
The corresponding Wilson-loop phase closes to unit holonomy at every integer
winding label on the calibrated bridge radius.
-/
theorem wilsonPhase_of_calibrated_winding
    (B : BridgeData (E := E)) (n : ℤ) :
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) := by
  exact wilsonPhase_of_winding (R := B.radius) B.radius_pos n

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

end Bridge

end InfoGeometry.Canonical.ThermalTimeMonodromyBridge
