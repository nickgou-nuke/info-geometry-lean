import Mathlib
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
Spin-modular compatibility witness.

This says the spin connection supplies the physical boost/Rindler flow that is
identified with modular flow after a normalization.
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

  /--
  Flow calibration law.

  Intended meaning: modular time and physical boost time differ by the
  Bisognano-Wichmann/Unruh normalization.
  -/
  modular_physical_calibration_law : Prop

  /-- Evidence for the modular/physical flow calibration. -/
  modular_physical_calibration :
    modular_physical_calibration_law

  /-- Spin-connection/boost compatibility law. -/
  spin_connection_generates_boost_law : Prop

  /-- Evidence for spin-connection/boost compatibility. -/
  spin_connection_generates_boost :
    spin_connection_generates_boost_law

namespace SpinModularCompatibility

variable {State : Type*}
variable (S : SpinModularCompatibility State)

/-- Re-export of positive acceleration. -/
theorem acceleration_positive :
    0 < S.acceleration :=
  S.acceleration_pos

/-- Re-export of the modular/physical flow calibration. -/
theorem modular_physical_calibration_valid :
    S.modular_physical_calibration_law :=
  S.modular_physical_calibration

/-- Re-export of the spin-connection/boost compatibility law. -/
theorem spin_connection_generates_boost_valid :
    S.spin_connection_generates_boost_law :=
  S.spin_connection_generates_boost

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

/--
The boost/KMS normalization certificate required for the Unruh temperature.
-/
theorem modular_physical_calibration_valid :
    U.spinModular.modular_physical_calibration_law :=
  U.spinModular.modular_physical_calibration_valid

/--
The spin-connection/boost generation certificate required for the Unruh
temperature.
-/
theorem spin_connection_generates_boost_valid :
    U.spinModular.spin_connection_generates_boost_law :=
  U.spinModular.spin_connection_generates_boost_valid

end UnruhTemperatureCalibration

/-! ## Constructive modular acceleration normalization -/

/--
Modular acceleration calibration.

This is the constructive natural-unit Unruh socket.  The final temperature
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
    (Op : Type*) [Mul Op]
    (σ : OperatorFlow Op)
    (beta : ℝ) where
  /-- Proper acceleration of the observer. -/
  acceleration : ℝ

  /-- Positive acceleration. -/
  acceleration_pos :
    0 < acceleration

  /-- Modular flow is geometrically calibrated as boost/Rindler time. -/
  modular_flow_is_boost_flow : Prop

  /-- Evidence for the modular/boost calibration. -/
  modular_flow_is_boost_flow_holds :
    modular_flow_is_boost_flow

  /-- Physical inverse temperature normalization. -/
  beta_eq_unruhBeta :
    beta = unruhBeta acceleration

namespace ModularBoostTemperatureCalibration

variable {Op : Type*} [Mul Op]
variable {σ : OperatorFlow Op}
variable {beta : ℝ}
variable (C : ModularBoostTemperatureCalibration Op σ beta)

/-- Re-export of the geometric boost-flow calibration. -/
theorem modular_flow_is_boost_flow_valid :
    C.modular_flow_is_boost_flow :=
  C.modular_flow_is_boost_flow_holds

/--
The calibrated physical temperature is `a / 2π`.
-/
theorem temperature_eq_unruh :
    1 / beta = unruhTemperature C.acceleration := by
  rcases C with ⟨a, ha, _hBoost, _hBoostValid, hbeta⟩
  subst beta
  unfold unruhBeta unruhTemperature
  field_simp [ne_of_gt ha, Real.pi_ne_zero]

end ModularBoostTemperatureCalibration

/--
Owner target for deriving the modular acceleration calibration from geometric
horizon/boost data.
-/
@[owner_target_tag]
def ModularUnruhCalibrationOwnerTarget : Prop :=
  Nonempty ModularAccelerationCalibration

/-! ## Owner target -/

/--
Owner target for installing a spin-modular Unruh temperature calibration.
-/
def SpinUnruhCalibrationOwnerTarget
    (State : Type*) : Prop :=
  Nonempty (UnruhTemperatureCalibration State)

attribute [rep_depth operator]
  SpinModularCompatibility
  SpinModularCompatibility.acceleration_positive
  SpinModularCompatibility.modular_physical_calibration_valid
  SpinModularCompatibility.spin_connection_generates_boost_valid
  unruhTemperatureNatural
  UnruhTemperatureCalibration
  UnruhTemperatureCalibration.temperature_eq_acceleration_over_two_pi
  UnruhTemperatureCalibration.modular_physical_calibration_valid
  UnruhTemperatureCalibration.spin_connection_generates_boost_valid
  ModularAccelerationCalibration
  ModularAccelerationCalibration.modular_beta_eq_two_pi
  ModularAccelerationCalibration.physical_beta
  ModularAccelerationCalibration.unruh_temperature
  unruhTemperature
  unruhBeta
  ModularBoostTemperatureCalibration
  ModularBoostTemperatureCalibration.modular_flow_is_boost_flow_valid
  ModularBoostTemperatureCalibration.temperature_eq_unruh
  ModularUnruhCalibrationOwnerTarget
  SpinUnruhCalibrationOwnerTarget

end InfoGeometry.OperatorAlgebra.SpinUnruhCalibration
