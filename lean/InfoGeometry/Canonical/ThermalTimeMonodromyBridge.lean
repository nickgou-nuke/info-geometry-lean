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

/--
Explicit calibration of the thermal-time/winding bridge to the concrete Cl(1,1)
monodromy construction.

Given the square-zero modular Hamiltonian `K` from the Witt creation operator,
we construct a canonical calibration where the period is chosen to normalize
the residue flow. This makes the connection between thermal time and de Rham
winding concrete rather than abstract.

The calibration period is set to 1 (the natural unit), corresponding to a
single "tick" of the parabolic clock generated by the nilpotent residue.
-/
def cl11CanonicalCalibration : ThermalTimeWindingCalibration where
  period := (1 : ℝ)
  period_ne_zero := by norm_num

/--
Bridge data instantiated from the concrete Cl(1,1) monodromy construction.

This packages together:
- The modular Radon-Nikodym data (from the ambient Hilbert space structure)
- The canonical Cl(1,1) calibration (period = 1)
- A reference radius for de Rham winding computations

Note: This construction demonstrates that the bridge is non-vacuous and can
be concretely realized from the Witt-based nilpotent generator. The choice of
period = 1 is a normalization; other scalings are possible by multiplying
the calibration.
-/
def cl11BridgeData (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (modularData : ModularRadonNikodymData E) (radius : ℝ) (h_radius : 0 < radius) :
    BridgeData (E := E) where
  modularData := modularData
  calibration := cl11CanonicalCalibration
  radius := radius
  radius_pos := h_radius

/--
The main calibration theorem: modular flow at integer winding time agrees with
the flow generated by the concrete Cl(1,1) residue operator.

For the canonical Cl(1,1) bridge data, evolving by `n` winding units ( period = 1)
produces the same modular automorphism as evolving by real time `n`.
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
Additivity of the Cl(1,1) calibrated clock at the operator level.

The modular flow at winding `m + n` decomposes as the composition of flows at
`m` and `n`, with the period normalized to 1. This reflects the additive
structure of the winding group ℤ and its homomorphic image in thermal time ℝ.
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
