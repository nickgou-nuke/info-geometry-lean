import Mathlib
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Thermo.RelativeTemperatureFirstLaw

Finite scalar first-law bridge:

  dS = β * dQ
  T = β⁻¹
  therefore dQ = T * dS

This is a scalar readout theorem. It is not an unbounded modular-operator
theorem.
-/

noncomputable section

namespace InfoGeometry.Thermo.RelativeTemperatureFirstLaw

/--
State-relative thermal readout.

`dQ` is the reversible heat/energy variation relative to a chosen reference.
`dS` is the entropy variation.
`β` is inverse temperature.
`T` is temperature.
-/
@[rep_depth thermo]
structure RelativeTemperatureDatum where
  dQ : ℝ
  dS : ℝ
  β : ℝ
  T : ℝ

  /-- Inverse-temperature form of the reversible first law. -/
  firstLaw_inverse : dS = β * dQ

  /-- Temperature is inverse modular scale. -/
  temperature_eq_inv_beta : T = β⁻¹

namespace RelativeTemperatureDatum

variable (D : RelativeTemperatureDatum)

/--
If `β ≠ 0`, then the usual reversible heat form follows:

`dQ = T * dS`.
-/
@[rep_depth thermo]
theorem temperature_mul_entropy_eq_heat
    (hβ : D.β ≠ 0) :
    D.T * D.dS = D.dQ := by
  calc
    D.T * D.dS = D.β⁻¹ * (D.β * D.dQ) := by
      rw [D.temperature_eq_inv_beta, D.firstLaw_inverse]
    _ = (D.β⁻¹ * D.β) * D.dQ := by
      simp [mul_assoc]
    _ = D.dQ := by
      rw [inv_mul_cancel₀ hβ, one_mul]

/--
If `dQ ≠ 0`, then inverse temperature is the entropy/heat derivative:

`β = dS / dQ`.
-/
@[rep_depth thermo]
theorem invTemperature_eq_entropy_div_heat
    (hQ : D.dQ ≠ 0) :
    D.β = D.dS / D.dQ := by
  calc
    D.β = (D.β * D.dQ) / D.dQ := by
      field_simp [hQ]
    _ = D.dS / D.dQ := by
      rw [D.firstLaw_inverse]

/--
Equivalent statement:

`1 / T = dS / dQ`, assuming both scales are nonzero.
-/
@[rep_depth thermo]
theorem invTemperature_as_inv_T_eq_entropy_div_heat
    (hβ : D.β ≠ 0)
    (hQ : D.dQ ≠ 0) :
    D.T⁻¹ = D.dS / D.dQ := by
  calc
    D.T⁻¹ = (D.β⁻¹)⁻¹ := by
      rw [D.temperature_eq_inv_beta]
    _ = D.β := by
      simpa using inv_inv₀ hβ
    _ = D.dS / D.dQ := D.invTemperature_eq_entropy_div_heat hQ

end RelativeTemperatureDatum

end InfoGeometry.Thermo.RelativeTemperatureFirstLaw
