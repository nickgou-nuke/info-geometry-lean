import InfoGeometry.Canonical.BogoliubovClosedForms

/-!
# Quarter-turn consequences of the modular phase flow

The continuous `KRotation` flow is kept on its native doubled-space carrier.
This owner records the finite quarter-turn consequences without identifying
that carrier with a local `Cl(1,1)` matrix slice.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.KRotationQuarterTurnFiniteSubgroup

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

theorem KRotation_quarter_apply (u : H₂) :
    KRotation (E := E) (Real.pi / 2) u = clockAxis (E := E) u := by
  simp [KRotation_apply, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The quarter-turn propagator is exactly its native phase-axis operator. -/
theorem KRotation_quarter_eq_clockAxis :
    KRotation (E := E) (Real.pi / 2) = clockAxis (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  exact KRotation_quarter_apply u

theorem KRotation_half_apply (u : H₂) :
    KRotation (E := E) Real.pi u = -u := by
  simp [KRotation_apply, Real.cos_pi, Real.sin_pi]

theorem KRotation_three_quarter_apply (u : H₂) :
    KRotation (E := E) (3 * Real.pi / 2) u = -(clockAxis (E := E) u) := by
  rw [KRotation_apply]
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring]
    simp [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
  have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring]
    simp [Real.sin_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
  rw [hcos, hsin]
  simp

theorem KRotation_full_period :
    KRotation (E := E) (2 * Real.pi) = (1 : EndH) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [KRotation_apply]
  rw [show 2 * Real.pi = Real.pi + Real.pi by ring]
  simp [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi]

theorem KRotation_quarter_fourth_power :
    KRotation (E := E) (Real.pi / 2) *
        KRotation (E := E) (Real.pi / 2) *
        KRotation (E := E) (Real.pi / 2) *
        KRotation (E := E) (Real.pi / 2) = (1 : EndH) := by
  rw [← KRotation_add, ← KRotation_add, ← KRotation_add]
  convert KRotation_full_period (E := E) using 1 <;> ring

end InfoGeometry.Canonical.KRotationQuarterTurnFiniteSubgroup
