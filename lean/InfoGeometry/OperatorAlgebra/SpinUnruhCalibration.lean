import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

/-!
# Spin-Unruh Calibration

Spin-modular compatibility and Unruh temperature normalization.

The modular flow gives KMS thermality.  The natural-unit Unruh temperature
appears only after a geometric calibration identifies modular flow with
physical boost/Rindler time for an observer with proper acceleration `a`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpinUnruhCalibration

open InfoGeometry.OperatorAlgebra.OperatorThermodynamics

/--
Spin-modular compatibility carrier.

This stores the two flows and the positive acceleration readout.  It does not
certify the geometric identification of those flows; that remains an owner
target unless supplied by a concrete horizon/boost model.
-/
structure SpinModularCompatibility
    (State : Type*) where
  /-- Modular parameter flow. -/
  modularFlow : ℝ → State → State

  /-- Physical boost/Rindler flow. -/
  physicalBoostFlow : ℝ → State → State

  /-- Proper acceleration readout. -/
  acceleration : ℝ

  /-- Acceleration is positive. -/
  acceleration_pos : 0 < acceleration

namespace SpinModularCompatibility

variable {State : Type*}
variable (S : SpinModularCompatibility State)

/-- Re-export of positive acceleration. -/
theorem acceleration_positive :
    0 < S.acceleration :=
  S.acceleration_pos

end SpinModularCompatibility

/--
Natural-unit Unruh temperature.

`T = a / (2π)`.
-/
noncomputable def unruhTemperatureNatural
    {State : Type*}
    (S : SpinModularCompatibility State) : ℝ :=
  S.acceleration / (2 * Real.pi)

/--
Unruh calibration datum.

The equality is carried as a model certificate because it depends on the
normalization of modular flow, physical time, and units.
-/
structure UnruhTemperatureCalibration
    (State : Type*) where
  /-- Spin-modular/boost compatibility witness. -/
  spinModular :
    SpinModularCompatibility State

  /-- Physical temperature readout. -/
  temperature : ℝ

  /-- Calibration law in natural units. -/
  temperature_eq_unruh :
    temperature = unruhTemperatureNatural spinModular

namespace UnruhTemperatureCalibration

variable {State : Type*}
variable (U : UnruhTemperatureCalibration State)

/--
The calibrated temperature is `a / (2π)` in natural units.
-/
theorem temperature_eq_acceleration_over_two_pi :
    U.temperature =
      U.spinModular.acceleration / (2 * Real.pi) :=
  U.temperature_eq_unruh

end UnruhTemperatureCalibration

/-! ## Constructive modular acceleration normalization -/

/--
Modular acceleration calibration.

This is the constructive natural-unit Unruh calibration.  The final temperature
formula is not stored as a hypothesis: it is derived from the physical inverse
temperature calibration `β = 2π / a` and the definition `T = β⁻¹`.
-/
structure ModularAccelerationCalibration where
  /-- Proper acceleration, in natural units. -/
  acceleration : ℝ

  /-- Nonzero acceleration. -/
  acceleration_ne_zero : acceleration ≠ 0

  /-- Dimensionless modular inverse temperature. -/
  betaModular : ℝ

  /-- Modular KMS period/inverse temperature is `2π`. -/
  betaModular_eq_two_pi :
    betaModular = 2 * Real.pi

  /-- Physical inverse temperature. -/
  betaPhysical : ℝ

  /-- Calibration from modular to proper time: `β = 2π / a`. -/
  betaPhysical_eq :
    betaPhysical = (2 * Real.pi) / acceleration

  /-- Physical temperature in natural units. -/
  temperature : ℝ

  /-- Temperature is inverse physical beta. -/
  temperature_eq_inv_beta :
    temperature = betaPhysical⁻¹

namespace ModularAccelerationCalibration

variable (C : ModularAccelerationCalibration)

/-- Re-export of the modular KMS normalization. -/
theorem modular_beta_eq_two_pi :
    C.betaModular = 2 * Real.pi :=
  C.betaModular_eq_two_pi

/-- Re-export of the physical inverse-temperature calibration. -/
theorem physical_beta :
    C.betaPhysical = (2 * Real.pi) / C.acceleration :=
  C.betaPhysical_eq

/--
Natural-unit Unruh temperature derived from the acceleration/beta calibration.
-/
theorem unruh_temperature :
    C.temperature = C.acceleration / (2 * Real.pi) := by
  rw [C.temperature_eq_inv_beta, C.betaPhysical_eq]
  field_simp [C.acceleration_ne_zero, Real.pi_ne_zero]

end ModularAccelerationCalibration

/--
Natural-units Unruh temperature readout for a proper acceleration `a`.
-/
noncomputable def unruhTemperature
    (a : ℝ) : ℝ :=
  a / (2 * Real.pi)

/--
Natural-units Unruh inverse temperature readout for a proper acceleration `a`.
-/
noncomputable def unruhBeta
    (a : ℝ) : ℝ :=
  (2 * Real.pi) / a

/--
Calibration identifying modular/KMS time with physical Rindler/horizon boost
time.

The value `beta = 2π / a` is not a consequence of an abstract modular flow
alone; it comes from the geometric normalization of the boost parameter.
-/
structure ModularBoostTemperatureCalibration
    (Op : Type*) [Monoid Op]
    (σ : OperatorFlow Op)
    (beta : ℝ) where
  /-- Proper acceleration of the observer. -/
  acceleration : ℝ

  /-- Positive acceleration. -/
  acceleration_pos :
    0 < acceleration

  /-- Physical inverse temperature normalization. -/
  beta_eq_unruhBeta :
    beta = unruhBeta acceleration

namespace ModularBoostTemperatureCalibration

variable {Op : Type*} [Monoid Op]
variable {σ : OperatorFlow Op}
variable {beta : ℝ}
variable (C : ModularBoostTemperatureCalibration Op σ beta)

/--
The calibrated physical temperature is `a / 2π`.
-/
theorem temperature_eq_unruh :
    1 / beta = unruhTemperature C.acceleration := by
  rcases C with ⟨a, ha, hbeta⟩
  subst beta
  unfold unruhBeta unruhTemperature
  field_simp [ne_of_gt ha, Real.pi_ne_zero]

end ModularBoostTemperatureCalibration

/-! ## Owner theorems -/

/-- A concrete natural-unit modular acceleration calibration at acceleration `1`. -/
def unitModularAccelerationCalibration : ModularAccelerationCalibration where
  acceleration := 1
  acceleration_ne_zero := by norm_num
  betaModular := 2 * Real.pi
  betaModular_eq_two_pi := rfl
  betaPhysical := 2 * Real.pi
  betaPhysical_eq := by
    field_simp
  temperature := (2 * Real.pi)⁻¹
  temperature_eq_inv_beta := rfl

/-- The concrete unit modular acceleration calibration has the Unruh readout laws. -/
theorem modularUnruhCalibrationOwnerTarget :
    unitModularAccelerationCalibration.betaModular = 2 * Real.pi ∧
      unitModularAccelerationCalibration.betaPhysical =
        (2 * Real.pi) / unitModularAccelerationCalibration.acceleration ∧
      unitModularAccelerationCalibration.temperature =
        unitModularAccelerationCalibration.acceleration / (2 * Real.pi) := by
  exact ⟨
    unitModularAccelerationCalibration.modular_beta_eq_two_pi,
    unitModularAccelerationCalibration.physical_beta,
    unitModularAccelerationCalibration.unruh_temperature⟩

/-- Identity spin-modular compatibility at unit acceleration. -/
def unitSpinModularCompatibility
    (State : Type*) : SpinModularCompatibility State where
  modularFlow := fun _ x => x
  physicalBoostFlow := fun _ x => x
  acceleration := 1
  acceleration_pos := by norm_num

/-- Concrete spin-modular Unruh calibration at unit acceleration. -/
def unitSpinUnruhCalibration
    (State : Type*) : UnruhTemperatureCalibration State where
  spinModular := unitSpinModularCompatibility State
  temperature := (2 * Real.pi)⁻¹
  temperature_eq_unruh := by
    unfold unruhTemperatureNatural unitSpinModularCompatibility
    field_simp [Real.pi_ne_zero]

/-- The concrete unit-acceleration spin-Unruh calibration has the readout laws. -/
theorem spinUnruhCalibrationOwnerTarget
    (State : Type*) :
    (unitSpinUnruhCalibration State).temperature =
        unruhTemperatureNatural (unitSpinUnruhCalibration State).spinModular ∧
      0 < (unitSpinUnruhCalibration State).spinModular.acceleration := by
  exact ⟨
    (unitSpinUnruhCalibration State).temperature_eq_unruh,
    (unitSpinUnruhCalibration State).spinModular.acceleration_positive⟩

attribute [rep_depth operator]
  SpinModularCompatibility
  SpinModularCompatibility.acceleration_positive
  unruhTemperatureNatural
  UnruhTemperatureCalibration
  UnruhTemperatureCalibration.temperature_eq_acceleration_over_two_pi
  ModularAccelerationCalibration
  ModularAccelerationCalibration.modular_beta_eq_two_pi
  ModularAccelerationCalibration.physical_beta
  ModularAccelerationCalibration.unruh_temperature
  unruhTemperature
  unruhBeta
  ModularBoostTemperatureCalibration
  ModularBoostTemperatureCalibration.temperature_eq_unruh
  unitModularAccelerationCalibration
  modularUnruhCalibrationOwnerTarget
  unitSpinModularCompatibility
  unitSpinUnruhCalibration
  spinUnruhCalibrationOwnerTarget

end InfoGeometry.OperatorAlgebra.SpinUnruhCalibration
