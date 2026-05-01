/-
InfoGeometry/OperatorAlgebra/UnruhTemperatureCalibration.lean

Unruh temperature from calibrated modular boost time.

This module is a thin public-facing facade over `SpinUnruhCalibration`.
It keeps the Unruh/Horizon thermodynamic normalization separate from the
material-optics susceptibility bridge.

The value `T = a / (2π)` is not derived from an abstract modular flow alone.
It is derived only after a boost/proper-time calibration supplies
`β = 2π / a`.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.SpinUnruhCalibration
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.OperatorAlgebra.UnruhTemperatureCalibration

open InfoGeometry.OperatorAlgebra.SpinUnruhCalibration

/-! ## Public aliases for the modular/boost branch -/

/-- Spin-modular compatibility witness from the Unruh branch. -/
abbrev SpinModularCompatibility :=
  SpinUnruhCalibration.SpinModularCompatibility

/-- Witness-gated spin/boost Unruh temperature calibration. -/
abbrev SpinBoostUnruhTemperatureCalibration :=
  SpinUnruhCalibration.UnruhTemperatureCalibration

/-- Constructive modular acceleration calibration. -/
abbrev ModularAccelerationCalibration :=
  SpinUnruhCalibration.ModularAccelerationCalibration

/-- Modular boost temperature calibration. -/
abbrev ModularBoostTemperatureCalibration :=
  SpinUnruhCalibration.ModularBoostTemperatureCalibration

/-- Natural-unit Unruh temperature `a / (2π)`. -/
abbrev unruhTemperature :=
  SpinUnruhCalibration.unruhTemperature

/-- Natural-unit inverse Unruh temperature `2π / a`. -/
abbrev unruhBeta :=
  SpinUnruhCalibration.unruhBeta

/-! ## Constructive readout theorems -/

namespace ModularAccelerationCalibration

variable (C : ModularAccelerationCalibration)

/--
The physical inverse temperature is `β = 2π / a` once the boost-time
normalization is supplied.
-/
theorem beta_eq_two_pi_div_acceleration :
    C.betaPhysical = (2 * Real.pi) / C.acceleration :=
  C.physical_beta

/--
The natural-unit Unruh temperature follows from
`β = 2π / a` and `T = β⁻¹`.
-/
theorem temperature_eq_acceleration_over_two_pi :
    C.temperature = C.acceleration / (2 * Real.pi) :=
  C.unruh_temperature

end ModularAccelerationCalibration

namespace ModularBoostTemperatureCalibration

variable {Op : Type*} [Mul Op]
variable {sigma : OperatorThermodynamics.OperatorFlow Op}
variable {beta : ℝ}
variable (C : ModularBoostTemperatureCalibration Op sigma beta)

/-- The supplied modular flow is calibrated as boost/Rindler time. -/
theorem boost_time_calibration_valid :
    C.modular_flow_is_boost_flow :=
  C.modular_flow_is_boost_flow_valid

/--
After boost-time normalization, the physical temperature is `a / (2π)`.
-/
theorem temperature_eq_acceleration_over_two_pi :
    1 / beta = C.acceleration / (2 * Real.pi) :=
  C.temperature_eq_unruh

end ModularBoostTemperatureCalibration

namespace SpinBoostUnruhTemperatureCalibration

variable {State : Type*}
variable (C : SpinBoostUnruhTemperatureCalibration State)

/--
The witness-gated spin/boost calibration reads out `T = a / (2π)`.
-/
theorem temperature_eq_acceleration_over_two_pi :
    C.temperature =
      C.spinModular.acceleration / (2 * Real.pi) :=
  SpinUnruhCalibration.UnruhTemperatureCalibration.temperature_eq_acceleration_over_two_pi C

end SpinBoostUnruhTemperatureCalibration

/-! ## Owner target -/

/--
Owner target for the separate Unruh temperature branch.

The branch remains witness-gated: a concrete horizon/Rindler/boost model must
supply the modular acceleration calibration.
-/
def UnruhTemperatureCalibrationOwnerTarget : Prop :=
  Nonempty ModularAccelerationCalibration

/--
The Unruh-temperature owner target is exactly the modular Unruh calibration
owner target from the spin-modular branch.
-/
theorem unruhTemperatureCalibrationOwnerTarget_iff :
    UnruhTemperatureCalibrationOwnerTarget ↔
      SpinUnruhCalibration.ModularUnruhCalibrationOwnerTarget :=
  Iff.rfl

attribute [rep_depth operator]
  SpinModularCompatibility
  SpinBoostUnruhTemperatureCalibration
  ModularAccelerationCalibration
  ModularAccelerationCalibration.beta_eq_two_pi_div_acceleration
  ModularAccelerationCalibration.temperature_eq_acceleration_over_two_pi
  ModularBoostTemperatureCalibration
  ModularBoostTemperatureCalibration.boost_time_calibration_valid
  ModularBoostTemperatureCalibration.temperature_eq_acceleration_over_two_pi
  unruhTemperature
  unruhBeta
  UnruhTemperatureCalibrationOwnerTarget
  unruhTemperatureCalibrationOwnerTarget_iff

end InfoGeometry.OperatorAlgebra.UnruhTemperatureCalibration
