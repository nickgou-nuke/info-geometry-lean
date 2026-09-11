import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Real

namespace InfoGeometry.Canonical.UnruhTemperatureAccelerationBridge

/-- 1. Unruh Thermal Radiation Acceleration Temperature T_Unruh(a) = (ℏ a) / (2π c k_B) -/
noncomputable def unruhTemperature (acc hbar c kB : ℝ) : ℝ :=
  (hbar * acc) / (2 * Real.pi * c * kB)

/-- 🏆 THEOREM 1: Unruh Acceleration Temperature Linearity under Composite Acceleration:
    T_Unruh(a₁ + a₂) = T_Unruh(a₁) + T_Unruh(a₂) -/
theorem unruh_temperature_add (a1 a2 hbar c kB : ℝ) :
    unruhTemperature (a1 + a2) hbar c kB =
      unruhTemperature a1 hbar c kB + unruhTemperature a2 hbar c kB := by
  dsimp [unruhTemperature]
  ring

/-- 🏆 THEOREM 2: Unruh Thermal Radiation Temperature Non-negativity:
    a ≥ 0, ℏ > 0, c > 0, k_B > 0 ⇒ T_Unruh(a) ≥ 0 -/
theorem unruh_temperature_nonneg (acc hbar c kB : ℝ) (ha : 0 ≤ acc) (hh : 0 < hbar)
    (hc : 0 < c) (hk : 0 < kB) :
    0 ≤ unruhTemperature acc hbar c kB := by
  dsimp [unruhTemperature]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnum : 0 ≤ hbar * acc := mul_nonneg (le_of_lt hh) ha
  have hden : 0 < 2 * Real.pi * c * kB := by
    have h1 : 0 < 2 * Real.pi := mul_pos (by norm_num) hpi
    have h2 : 0 < 2 * Real.pi * c := mul_pos h1 hc
    exact mul_pos h2 hk
  exact div_nonneg hnum (le_of_lt hden)

/-- 🏆 THEOREM 3: Vanishing Unruh Temperature for Inertial Observers (a = 0):
    T_Unruh(0) = 0 -/
theorem unruh_temperature_zero (hbar c kB : ℝ) :
    unruhTemperature 0 hbar c kB = 0 := by
  dsimp [unruhTemperature]
  ring

end InfoGeometry.Canonical.UnruhTemperatureAccelerationBridge
