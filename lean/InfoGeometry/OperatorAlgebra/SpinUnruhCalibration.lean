import Mathlib
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Meta.Architecture

/-!
# Spin-Unruh Calibration

Spin-modular compatibility and Unruh temperature normalization.

The modular flow gives KMS thermality.  The natural-unit Unruh temperature
appears only after a geometric calibration identifies modular flow with
physical boost/Rindler time for an observer with proper acceleration `a`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpinUnruhCalibration

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
  SpinUnruhCalibrationOwnerTarget

end InfoGeometry.OperatorAlgebra.SpinUnruhCalibration

