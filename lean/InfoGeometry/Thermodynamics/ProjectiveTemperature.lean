/-
InfoGeometry/Thermodynamics/ProjectiveTemperature.lean

Projective temperature inversion for the finite Riemann-gas/primitive-set
objective.

This module formalizes the real, finite-temperature shadow of the geometric
picture

  beta ↦ beta⁻¹

and the stereographic parametrization of the positive temperature ray on a
circle.  It deliberately does not assert a Tomita theorem, a KMS existence
theorem, a modular-form theorem, or the Riemann hypothesis.  The actual
change-of-variables statement for the objective integral is exposed as an
explicit calibration witness.
-/

import Mathlib
import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints

noncomputable section

open scoped BigOperators

namespace ProjectiveTemperature

open InfoGeometry.Arithmetic
open MobiusClosureFixedPoints

/-! ## 1. Real temperature inversion -/

/--
Real finite-temperature inversion.

On the projective compactification this is the finite real shadow of swapping
`0` and `∞`.  On plain `ℝ`, Lean's total inverse sends `0` to `0`, so the
projective endpoints are intentionally not claimed here.
-/
def betaInvert (β : ℝ) : ℝ :=
  β⁻¹

/-- Temperature inversion is an involution on the real shadow. -/
theorem betaInvert_involutive (β : ℝ) :
    betaInvert (betaInvert β) = β := by
  simp [betaInvert]

/-- The critical point `β = 1` is fixed by inversion. -/
theorem betaInvert_one :
    betaInvert 1 = 1 := by
  simp [betaInvert]

/-- Positive temperatures stay positive under inversion. -/
theorem betaInvert_pos {β : ℝ} (hβ : 0 < β) :
    0 < betaInvert β := by
  exact inv_pos.mpr hβ

/-- The low-temperature ray `(1, ∞)` maps into the high-temperature interval `(0, 1)`. -/
theorem betaInvert_mem_Ioo_zero_one_of_one_lt {β : ℝ} (hβ : 1 < β) :
    betaInvert β ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact betaInvert_pos (lt_trans zero_lt_one hβ)
  · simpa [betaInvert] using inv_lt_one_of_one_lt₀ hβ

/-- The high-temperature interval `(0, 1)` maps into the low-temperature ray `(1, ∞)`. -/
theorem one_lt_betaInvert_of_mem_Ioo_zero_one {β : ℝ}
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    1 < betaInvert β := by
  simpa [betaInvert] using (one_lt_inv₀ hβ.1).mpr hβ.2

/--
The real-shadow closure involution associated to temperature inversion.

This connects the thermodynamic temperature ray to the existing abstract
Möbius/Tomita fixed-point socket without claiming that this real map is itself
a Tomita operator.
-/
def temperatureClosureInvolution : ClosureInvolution ℝ where
  theta := betaInvert
  theta_sq := betaInvert_involutive

/-- The critical point `1` is fixed by the temperature closure involution. -/
theorem one_isFixed_temperatureClosure :
    temperatureClosureInvolution.IsFixed 1 := by
  simp [temperatureClosureInvolution, ClosureInvolution.IsFixed, betaInvert]

/-! ## 2. Stereographic circle coordinates -/

/--
The `x`-coordinate of the positive real ray on the projective temperature
circle:

`β ↦ 2β / (β² + 1)`.
-/
def stereographicTemperatureX (β : ℝ) : ℝ :=
  (2 * β) / (β ^ 2 + 1)

/--
The `y`-coordinate of the positive real ray on the projective temperature
circle:

`β ↦ (β² - 1) / (β² + 1)`.
-/
def stereographicTemperatureY (β : ℝ) : ℝ :=
  (β ^ 2 - 1) / (β ^ 2 + 1)

/-- The projective temperature point on the circle. -/
def stereographicTemperature (β : ℝ) : ℝ × ℝ :=
  (stereographicTemperatureX β, stereographicTemperatureY β)

/-- The infinite-temperature endpoint shadow `β = 0` maps to the south pole. -/
theorem stereographicTemperature_zero :
    stereographicTemperature 0 = (0, -1) := by
  ext <;> simp [stereographicTemperature, stereographicTemperatureX,
    stereographicTemperatureY]

/-- The fixed critical temperature `β = 1` maps to the equator point `(1, 0)`. -/
theorem stereographicTemperature_one :
    stereographicTemperature 1 = (1, 0) := by
  ext <;> norm_num [stereographicTemperature, stereographicTemperatureX,
    stereographicTemperatureY]

/-- The stereographic temperature point lies on the unit circle. -/
theorem stereographicTemperature_on_unit_circle (β : ℝ) :
    stereographicTemperatureX β ^ 2 + stereographicTemperatureY β ^ 2 = 1 := by
  have hden : β ^ 2 + 1 ≠ 0 := by
    have hpos : 0 < β ^ 2 + 1 := by nlinarith [sq_nonneg β]
    exact hpos.ne'
  unfold stereographicTemperatureX stereographicTemperatureY
  field_simp [hden]
  ring

/-! ## 3. Primitive objective under inverted temperature coordinates -/

/--
Finite Riemann-gas partition restricted to a finite arithmetic support.

This is the same finite sum that appears under the integral in
`primitiveWeightSum_eq_integral_mellinKernel`.
-/
def primitiveRestrictedPartition (A : Finset ℕ) (β : ℝ) : ℝ :=
  Finset.sum A (fun n => primitiveMellinKernel n β)

/--
The formal density obtained from the substitution `u = β⁻¹`.

The Jacobian factor for `β = u⁻¹` is represented as `(u^2)⁻¹`.  The equality
between the original integral over `(1, ∞)` and this inverted integral over
`(0, 1)` is supplied by `PrimitiveTemperatureInversionCalibration`.
-/
def primitiveInvertedPartitionDensity (A : Finset ℕ) (u : ℝ) : ℝ :=
  (u ^ 2)⁻¹ * primitiveRestrictedPartition A (betaInvert u)

/--
Witness that the projective temperature inversion correctly transports the
finite primitive/Riemann-gas objective integral.

This is a calibration socket, not a proof of a general measure-substitution
theorem.
-/
structure PrimitiveTemperatureInversionCalibration
    (A : Finset ℕ) where
  /-- The supplied change-of-variables law for the restricted partition. -/
  inversion_integral :
    (∫ β : ℝ in Set.Ioi 1, primitiveRestrictedPartition A β)
      =
    ∫ u : ℝ in Set.Ioo 0 1, primitiveInvertedPartitionDensity A u

/--
The primitive weight objective can be read on the compact inverted temperature
interval once the inversion calibration is supplied.
-/
theorem PrimitiveTemperatureInversionCalibration.primitiveWeightSum_eq_inverted_temperature_integral
    {A : Finset ℕ} (C : PrimitiveTemperatureInversionCalibration A) :
    primitiveWeightSum A =
      ∫ u : ℝ in Set.Ioo 0 1, primitiveInvertedPartitionDensity A u := by
  rw [primitiveWeightSum_eq_integral_mellinKernel A]
  exact PrimitiveTemperatureInversionCalibration.inversion_integral C

end ProjectiveTemperature
