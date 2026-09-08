import InfoGeometry.Nuclear.FocalRapidity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# An actual differential equation for the focal sech profile

This module goes beyond an algebraic resemblance to a soliton: it proves the
stationary profile equation `f'' = f - 2 * f^3` for `f = 1 / cosh`, using
Mathlib derivatives. No time-dependent PDE, scattering theorem, stability
statement, or detector propagation law is asserted.
-/

noncomputable section

namespace InfoGeometry.Nuclear.FocalRapidity

/-- Explicit first derivative of `sechProfile`. -/
def sechSlope (x : ℝ) : ℝ :=
  -Real.sinh x / Real.cosh x ^ 2

theorem hasDerivAt_sechProfile (x : ℝ) :
    HasDerivAt sechProfile (sechSlope x) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).div
    (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  simpa [sechProfile, sechSlope] using h

theorem deriv_sechProfile : deriv sechProfile = sechSlope :=
  funext fun x => (hasDerivAt_sechProfile x).deriv

/-- Quotient-rule derivative before applying the hyperbolic quadratic identity. -/
theorem hasDerivAt_sechSlope_raw (x : ℝ) :
    HasDerivAt sechSlope
      (-1 / Real.cosh x + 2 * Real.sinh x ^ 2 / Real.cosh x ^ 3) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := ((Real.hasDerivAt_sinh x).neg).div
    ((Real.hasDerivAt_cosh x).pow 2) (pow_ne_zero 2 hc)
  convert h using 1 <;> dsimp [sechSlope] <;> field_simp [hc] <;> ring

theorem hasDerivAt_sechSlope (x : ℝ) :
    HasDerivAt sechSlope (sechProfile x - 2 * sechProfile x ^ 3) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  convert hasDerivAt_sechSlope_raw x using 1
  dsimp [sechProfile]
  rw [Real.sinh_sq]
  field_simp [hc] <;> ring

/-- Exact nonlinear stationary profile equation, stated with actual derivatives. -/
theorem sech_stationary_ode (x : ℝ) :
    deriv (deriv sechProfile) x = sechProfile x - 2 * sechProfile x ^ 3 := by
  rw [deriv_sechProfile]
  exact (hasDerivAt_sechSlope x).deriv

/-- First integral of the stationary equation for this particular profile. -/
theorem sech_energy_identity (x : ℝ) :
    (deriv sechProfile x) ^ 2 = sechProfile x ^ 2 - sechProfile x ^ 4 := by
  rw [deriv_sechProfile]
  dsimp [sechSlope, sechProfile]
  simp only [div_pow, neg_sq]
  rw [Real.sinh_sq]
  field_simp [ne_of_gt (Real.cosh_pos x)] <;> ring

@[simp] theorem sechProfile_zero : sechProfile 0 = 1 := by
  simp [sechProfile]

@[simp] theorem sechProfile_neg (x : ℝ) : sechProfile (-x) = sechProfile x := by
  simp [sechProfile]

end InfoGeometry.Nuclear.FocalRapidity
