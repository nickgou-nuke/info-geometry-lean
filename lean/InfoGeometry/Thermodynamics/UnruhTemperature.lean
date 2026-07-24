import Mathlib
import InfoGeometry.Canonical.WedgeBoostModularBridge

/-!
# Unruh Temperature Derivation

This module formalizes the Unruh temperature derivation for a uniformly accelerating
observer in the Rindler wedge.

We prove:
1. **The Rindler Boost/Proper Time Relation:**
   The boost rapidity is given by $\theta = a \cdot \tau$, where $a$ is the constant
   proper acceleration and $\tau$ is the proper time.
2. **The Modular Time Identification:**
   From the Wedge-Boost Modular Bridge, the boost parameter is related to the modular time
   by $\theta = 2\pi \cdot \tau_{mod}$.
3. **The Unruh Temperature Theorem:**
   By identifying the modular time period $\Delta \tau_{mod} = 1$ with the imaginary proper time
   period $\beta$, we obtain $\beta = \frac{2\pi}{a}$. This yields the Unruh temperature:
   $$ T_U = \frac{a}{2\pi} $$
   natively in the real doubled language.
-/

namespace InfoGeometry.Thermodynamics.UnruhTemperature

open InfoGeometry.Canonical.RealTomitaCore

/--
A structure representing the uniform acceleration context of a Rindler observer.
-/
structure RindlerObserver where
  /-- Constant proper acceleration (a > 0) -/
  a : ℝ
  /-- Acceleration is positive -/
  ha : 0 < a

/-- The boost rapidity as a function of proper time `τ`. -/
def rapidity (obs : RindlerObserver) (τ : ℝ) : ℝ :=
  obs.a * τ

/--
Identifying proper time `τ` and modular time `τmod` under the Unruh flow reparameterization.
This corresponds to setting `rapidity obs τ = wedgeBoostParameter τmod`.
-/
noncomputable def properTime_of_modularTime (obs : RindlerObserver) (τmod : ℝ) : ℝ :=
  (2 * Real.pi * τmod) / obs.a

/--
Theorem: The modular-time to proper-time conversion satisfies the boost parameter identification.
-/
theorem rapidity_properTime_eq_wedgeBoostParameter (obs : RindlerObserver) (τmod : ℝ) :
    rapidity obs (properTime_of_modularTime obs τmod) = wedgeBoostParameter τmod := by
  dsimp [rapidity, properTime_of_modularTime, wedgeBoostParameter]
  have h_ne : obs.a ≠ 0 := by
    exact ne_of_gt obs.ha
  rw [mul_div_cancel₀ _ h_ne]

/-- The modular period of the KMS state (normalized to 1). -/
def modularPeriod : ℝ := 1

/--
The proper time period (inverse temperature) β corresponding to the modular period.
-/
noncomputable def inverseTemperature (obs : RindlerObserver) : ℝ :=
  properTime_of_modularTime obs modularPeriod

/--
Theorem: The inverse temperature β of the accelerating observer is 2π / a.
-/
theorem inverseTemperature_eq (obs : RindlerObserver) :
    inverseTemperature obs = (2 * Real.pi) / obs.a := by
  dsimp [inverseTemperature, properTime_of_modularTime, modularPeriod]
  ring

/--
The Unruh temperature (T_U = 1 / β) in natural units where k_B = 1.
-/
noncomputable def unruhTemperature (obs : RindlerObserver) : ℝ :=
  (inverseTemperature obs)⁻¹

/--
Theorem: The Unruh temperature is strictly proportional to the acceleration:
$$ T_U = \frac{a}{2\pi} $$
-/
theorem unruhTemperature_eq (obs : RindlerObserver) :
    unruhTemperature obs = obs.a / (2 * Real.pi) := by
  dsimp [unruhTemperature]
  rw [inverseTemperature_eq]
  exact inv_div (2 * Real.pi) obs.a

end InfoGeometry.Thermodynamics.UnruhTemperature
