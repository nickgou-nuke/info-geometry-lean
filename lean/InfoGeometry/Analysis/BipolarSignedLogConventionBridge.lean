import InfoGeometry.Analysis.BipolarPeriodDescent
import Mathlib.Tactic

/-!
# Sign convention for the bipolar logarithmic coordinate

The repository's canonical coordinate is

`q(s)=s/(1-s)`.

The alternative convention in the informal stream is

`F(s)=s/(s-1)=-q(s)`.

They have the same logarithmic differential because multiplication by the
constant `-1` does not change `dF/F`.  Their principal logarithms are not the
same modulo `2πi` in general: exponentiation gives opposite nonzero values.
This file records the exact branch-safe statements and does not assert a global
identity between the two principal logarithms.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarSignedLogConventionBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarPeriodDescent

/-- Principal logarithmic readout of the sign-shifted coordinate `s/(s-1)`. -/
def signedBipolarLog (s : ℂ) : ℂ :=
  Complex.log (signedCrossRatio01 s)

/-- Exponentiation recovers the sign-shifted coordinate on the punctured
domain. -/
theorem exp_signedBipolarLog
    {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (signedBipolarLog s) = signedCrossRatio01 s := by
  exact Complex.exp_log (signedCrossRatio01_ne_zero hs)

/-- The two principal logarithmic readouts exponentiate to opposite values. -/
theorem exp_signedBipolarLog_eq_neg_exp_bipolarLog
    {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (signedBipolarLog s) =
      -Complex.exp (bipolarLog s) := by
  rw [exp_signedBipolarLog hs, exp_bipolarLog hs]
  rfl

/-- On a compatible local branch, the sign-shifted principal logarithm has the
same derivative `dq/q`. -/
theorem hasDerivAt_signedBipolarLog
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : signedCrossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt signedBipolarLog (dlog01 s) s := by
  have hcomp :=
    (Complex.hasDerivAt_log hslit).comp s
      (hasDerivAt_signedCrossRatio01 hs)
  have hcoeff :
      (signedCrossRatio01 s)⁻¹ * (-1 / (s - 1) ^ 2) = dlog01 s := by
    rw [mul_comm]
    exact signedCrossRatio01_logarithmicDerivative hs
  simpa [signedBipolarLog, hcoeff] using hcomp

/-- Ordinary derivative readout of the local signed logarithmic branch. -/
theorem deriv_signedBipolarLog
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : signedCrossRatio01 s ∈ Complex.slitPlane) :
    deriv signedBipolarLog s = dlog01 s := by
  exact (hasDerivAt_signedBipolarLog hs hslit).deriv

/-- The two principal logarithms do not represent the same `2πi`-period class:
their exponentials differ by the nontrivial factor `-1`. -/
theorem signedBipolarLog_not_periodEquivalent
    {s : ℂ} (hs : s ∈ punctured01) :
    ¬PeriodEquivalent (signedBipolarLog s) (bipolarLog s) := by
  intro hperiod
  have hexp := exp_eq_of_PeriodEquivalent hperiod
  rw [exp_signedBipolarLog hs, exp_bipolarLog hs] at hexp
  change -crossRatio01 s = crossRatio01 s at hexp
  have htwo : (2 : ℂ) * crossRatio01 s = 0 := by
    calc
      (2 : ℂ) * crossRatio01 s = crossRatio01 s + crossRatio01 s := by ring
      _ = -crossRatio01 s + crossRatio01 s := by rw [hexp]
      _ = 0 := by ring
  have hzero : crossRatio01 s = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact (crossRatio01_ne_zero hs) hzero

/-- Compact sign-convention packet. -/
theorem bipolar_signed_log_convention_packet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : signedCrossRatio01 s ∈ Complex.slitPlane) :
    signedCrossRatio01 s = s / (s - 1) ∧
      Complex.exp (signedBipolarLog s) = signedCrossRatio01 s ∧
      HasDerivAt signedBipolarLog (dlog01 s) s ∧
      ¬PeriodEquivalent (signedBipolarLog s) (bipolarLog s) := by
  exact ⟨signedCrossRatio01_eq_div hs,
    exp_signedBipolarLog hs,
    hasDerivAt_signedBipolarLog hs hslit,
    signedBipolarLog_not_periodEquivalent hs⟩

end InfoGeometry.Analysis.BipolarSignedLogConventionBridge
