/-
InfoGeometry/Arithmetic/PrimitivePrimeProjectiveTemperature.lean

Finite von Mangoldt / prime-weighted projective-temperature sidecar.

This module connects the scalar von Mangoldt partition readout
`arithmeticPrimePartition` from `PrimitiveSetsAbove` with the real projective
temperature inversion from `ProjectiveTemperature`.

It does not assert the logarithmic derivative theorem for `ζ`, the prime
number theorem, analytic continuation, or a global Euler product.  The
change-of-variables statement over the compact interval `(0, 1)` is supplied
as an explicit calibration witness.
-/

import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Thermodynamics.ProjectiveTemperature

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

open InfoGeometry.Arithmetic
open InfoGeometry.Thermodynamics.ProjectiveTemperature

/-! ## 1. Finite von Mangoldt partition under projective temperature -/

/--
Finite von Mangoldt / prime-weighted partition restricted to a finite support.

This is an alias to `arithmeticPrimePartition`, placed here to make the
projective-temperature lane explicit.
-/
def arithmeticPrimeRestrictedPartition (A : Finset ℕ) (β : ℝ) : ℝ :=
  arithmeticPrimePartition A β

/--
The compact-coordinate density obtained from the substitution `u = β⁻¹` in the
finite von Mangoldt partition.

The Jacobian factor for `β = u⁻¹` is represented by `(u^2)⁻¹`.
-/
def arithmeticPrimeInvertedPartitionDensity (A : Finset ℕ) (u : ℝ) : ℝ :=
  (u ^ 2)⁻¹ * arithmeticPrimeRestrictedPartition A (betaInvert u)

/-- The restricted prime partition is the existing arithmetic prime partition. -/
theorem arithmeticPrimeRestrictedPartition_eq
    (A : Finset ℕ) (β : ℝ) :
    arithmeticPrimeRestrictedPartition A β =
      arithmeticPrimePartition A β :=
  rfl

/-- The compact-coordinate prime density unfolds to the Jacobian-weighted readout. -/
theorem arithmeticPrimeInvertedPartitionDensity_eq
    (A : Finset ℕ) (u : ℝ) :
    arithmeticPrimeInvertedPartitionDensity A u =
      (u ^ 2)⁻¹ * arithmeticPrimePartition A (betaInvert u) :=
  rfl

/-- The finite von Mangoldt partition is nonnegative. -/
theorem arithmeticPrimeRestrictedPartition_nonneg
    (A : Finset ℕ) (β : ℝ) :
    0 ≤ arithmeticPrimeRestrictedPartition A β := by
  simpa [arithmeticPrimeRestrictedPartition] using
    arithmeticPrimePartition_nonneg A β

/-- The compact-coordinate von Mangoldt density is nonnegative. -/
theorem arithmeticPrimeInvertedPartitionDensity_nonneg
    (A : Finset ℕ) (u : ℝ) :
    0 ≤ arithmeticPrimeInvertedPartitionDensity A u := by
  unfold arithmeticPrimeInvertedPartitionDensity
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg u))
    (arithmeticPrimeRestrictedPartition_nonneg A (betaInvert u))

/--
On positive-weight states, the finite von Mangoldt partition is the ordinary
prime-weighted Gibbs sum.
-/
theorem arithmeticPrimeRestrictedPartition_eq_exp_sum_of_supportedAbove_two
    {A : Finset ℕ}
    (hA : SupportedAboveFinset 2 A)
    (β : ℝ) :
    arithmeticPrimeRestrictedPartition A β =
      Finset.sum A
        (fun n => realVonMangoldt n * Real.exp (-β * Real.log (n : ℝ))) := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 < n := lt_of_lt_of_le Nat.one_lt_two (hA hn)
  simp [primitiveMellinKernel, hn1]

/-! ## 2. Compact-interval calibration socket -/

/--
Witness that projective temperature inversion transports the finite von
Mangoldt partition integral from `(1, ∞)` to `(0, 1)`.

This is a calibration socket, not a proof of a general measure-substitution
theorem or an analytic statement about `ζ`.
-/
structure ArithmeticPrimeTemperatureInversionCalibration
    (A : Finset ℕ) where
  /-- Supplied compact-coordinate change-of-variables law. -/
  inversion_integral_True :
    (∫ β : ℝ in Set.Ioi 1, arithmeticPrimeRestrictedPartition A β)
      =
    ∫ u : ℝ in Set.Ioo 0 1, arithmeticPrimeInvertedPartitionDensity A u

/--
The integrated finite von Mangoldt partition can be read on the compact
projective temperature interval once the inversion calibration is supplied.
-/
theorem ArithmeticPrimeTemperatureInversionCalibration.primePartitionIntegral_eq_inverted_temperature_integral
    {A : Finset ℕ} (C : ArithmeticPrimeTemperatureInversionCalibration A) :
    (∫ β : ℝ in Set.Ioi 1, arithmeticPrimeRestrictedPartition A β)
      =
    ∫ u : ℝ in Set.Ioo 0 1, arithmeticPrimeInvertedPartitionDensity A u :=
  ArithmeticPrimeTemperatureInversionCalibration.inversion_integral_True C

end InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature
