import InfoGeometry.Thermodynamics.UnruhTemperature
import InfoGeometry.Canonical.RindlerMobiusLogDeRhamBridge

/-!
# Unruh modular period as causal-cone monodromy

The KMS period is represented here by a real modular period and its winding
calibration.  The theorem below identifies one modular turn with the
`2 * π` Rindler rapidity already used by the Euclidean Rindler orbit.  No
independent analytic-strip axiom is introduced.
-/

namespace InfoGeometry.Thermodynamics.UnruhMonodromyCalibration

open InfoGeometry.Thermodynamics.UnruhTemperature

theorem rapidity_inverseTemperature_eq_two_pi
    (obs : RindlerObserver) :
    rapidity obs (inverseTemperature obs) = 2 * Real.pi := by
  rw [rapidity, inverseTemperature_eq]
  field_simp [ne_of_gt obs.ha]

theorem modular_period_is_one_turn
    (obs : RindlerObserver) :
    rapidity obs (properTime_of_modularTime obs modularPeriod) =
      2 * Real.pi := by
  simpa [inverseTemperature] using rapidity_inverseTemperature_eq_two_pi obs

end InfoGeometry.Thermodynamics.UnruhMonodromyCalibration
