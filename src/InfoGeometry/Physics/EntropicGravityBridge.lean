import Mathlib.Data.Real.Basic

/-!
# Scalar cancellation for a temperature-style equation

The identities connecting a dissipation, a heat-transfer quantity, and an
entropy rate are hypotheses of a concrete model. This file states those
identities explicitly and proves only their algebraic consequences; it does
not package them as a physical witness structure or derive them from a fluid
or gravitational theory.
-/

namespace InfoGeometry.Physics

/-- If a common nonzero rate multiplies two scalar parameters to the same
value, those parameters are equal. -/
theorem scalar_parameter_eq_of_common_nonzero_factor
    (x y rate : ℝ) (hrate : rate ≠ 0)
    (h : x * rate = y * rate) : x = y := by
  exact (mul_right_inj' hrate).mp (by simpa [mul_comm] using h)

/-- Conditional temperature/gap cancellation from the three scalar model
equations. `totalRate_eq_rate` records that the rate in the equation of state
is the same nonzero rate used by the dissipation factorization. -/
theorem jacobson_temperature_eq_mass_gap
    (gap rate dissipation heat temperature totalRate : ℝ)
    (hrate : rate ≠ 0)
    (h_dissipation : dissipation = gap * rate)
    (h_eos : heat = temperature * totalRate)
    (h_identification : dissipation = heat)
    (h_totalRate : totalRate = rate) :
    temperature = gap := by
  have h_product : gap * rate = temperature * rate := by
    calc
      gap * rate = dissipation := h_dissipation.symm
      _ = heat := h_identification
      _ = temperature * rate := by rw [h_totalRate] at h_eos; exact h_eos
  exact (mul_right_inj' hrate).mp (by simpa [mul_comm] using h_product.symm)

/-- If the model's factored dissipation vanishes, one of its two factors is
zero. No geometric or thermodynamic interpretation is inferred from this
algebraic disjunction. -/
theorem gap_or_rate_zero_of_zero_dissipation
    (gap rate : ℝ) (h : gap * rate = 0) : gap = 0 ∨ rate = 0 :=
  mul_eq_zero.mp h

end InfoGeometry.Physics
