open InfoGeometry.Thermodynamics.ProjectiveTemperature
open InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature

/-! ## 1. Projective von Mangoldt partition flow -/

/--
Projected von Mangoldt partition evaluated at inverted temperature `u = 1 / β`.

This is the finite-support compact-temperature shadow of the prime-weighted
Dirichlet readout.  It is not an analytic assertion about `-ζ'/ζ`.
-/
def projectivePrimePartition (A : Finset ℕ) (u : ℝ) : ℝ :=
  arithmeticPrimePartition A (betaInvert u)

/-- The projective prime partition is the restricted prime partition at `β = u⁻¹`. -/
theorem projectivePrimePartition_eq_restricted
    (A : Finset ℕ) (u : ℝ) :
    projectivePrimePartition A u =
      arithmeticPrimeRestrictedPartition A (betaInvert u) :=
  rfl

/-- The projective prime partition is nonnegative. -/
theorem projectivePrimePartition_nonneg
    (A : Finset ℕ) (u : ℝ) :
    0 ≤ projectivePrimePartition A u := by
  simpa [projectivePrimePartition] using