import InfoGeometry.Analysis.BipolarSignedLogConventionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
import Mathlib.Tactic

/-!
# Schwarzian of the sign-shifted bipolar logarithm

The informal stream uses `F(s)=s/(s-1)`, whereas the repository's canonical
coordinate is `q(s)=s/(1-s)=-F(s)`.  Their local logarithms have the same first
and higher derivatives wherever the corresponding principal branch is
analytic.  Consequently they determine the same branch-independent Schwarzian
coefficient.
-/

noncomputable section

namespace InfoGeometry.Conformal.BipolarSignedLogSchwarzianBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarSignedLogConventionBridge
open InfoGeometry.Conformal.ComplexSchwarzianJet
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection

/-- Certified third-order derivative tower for the signed principal logarithm. -/
theorem local_signedBipolarLog_thirdJet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : signedCrossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt signedBipolarLog (logarithmicJet₁ s) s ∧
      HasDerivAt logarithmicJet₁ (logarithmicJet₂ s) s ∧
      HasDerivAt logarithmicJet₂ (logarithmicJet₃ s) s := by
  exact ⟨by
      simpa [logarithmicJet₁] using
        hasDerivAt_signedBipolarLog hs hslit,
    hasDerivAt_logarithmicJet₁ hs,
    hasDerivAt_logarithmicJet₂ hs⟩

/-- Exact quadratic-pole form for the signed logarithmic convention. -/
theorem signedBipolarLog_schwarzian_eq_rational
    {s : ℂ} (hs : s ∈ punctured01) :
    schwarzianJet
        (logarithmicJet₁ s) (logarithmicJet₂ s) (logarithmicJet₃ s) =
      1 / (2 * s ^ 2 * (s - 1) ^ 2) := by
  change bipolarSchwarzian s = _
  exact bipolarSchwarzian_eq_rational hs

/-- The signed logarithmic Schwarzian is one half the square of the common
logarithmic differential. -/
theorem signedBipolarLog_schwarzian_eq_half_dlog01_sq
    {s : ℂ} (hs : s ∈ punctured01) :
    schwarzianJet
        (logarithmicJet₁ s) (logarithmicJet₂ s) (logarithmicJet₃ s) =
      (1 / 2 : ℂ) * dlog01 s ^ 2 := by
  change bipolarSchwarzian s = _
  exact bipolarSchwarzian_eq_half_dlog01_sq hs

/-- Compact signed-log Schwarzian packet. -/
theorem bipolar_signed_log_schwarzian_packet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : signedCrossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt signedBipolarLog (logarithmicJet₁ s) s ∧
      HasDerivAt logarithmicJet₁ (logarithmicJet₂ s) s ∧
      HasDerivAt logarithmicJet₂ (logarithmicJet₃ s) s ∧
      schwarzianJet
          (logarithmicJet₁ s) (logarithmicJet₂ s) (logarithmicJet₃ s) =
        (1 / 2 : ℂ) * dlog01 s ^ 2 := by
  exact ⟨(local_signedBipolarLog_thirdJet hs hslit).1,
    (local_signedBipolarLog_thirdJet hs hslit).2.1,
    (local_signedBipolarLog_thirdJet hs hslit).2.2,
    signedBipolarLog_schwarzian_eq_half_dlog01_sq hs⟩

end InfoGeometry.Conformal.BipolarSignedLogSchwarzianBridge
