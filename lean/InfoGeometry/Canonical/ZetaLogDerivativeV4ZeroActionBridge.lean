import InfoGeometry.Canonical.ZetaLogDerivativeDeRhamPeriodBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# V₄ action laws on finite isolated-zero data

The period owner already transports multiplicities through the three finite
zero maps.  This file supplies the missing action laws on the data itself.
No contour, residue, or de Rham cohomology theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaLogDerivativeV4ZeroActionBridge

open InfoGeometry.Canonical.ZetaLogDerivativeDeRhamPeriod

theorem tauZero_involutive (z : IsolatedZeroData) :
    tauZero (tauZero z) = z := by
  cases z with
  | mk center multiplicity h_mult_pos =>
      simp [tauZero]

theorem sigmaZero_involutive (z : IsolatedZeroData) :
    sigmaZero (sigmaZero z) = z := by
  cases z with
  | mk center multiplicity h_mult_pos =>
      simp [sigmaZero]

theorem gammaZero_involutive (z : IsolatedZeroData) :
    gammaZero (gammaZero z) = z := by
  cases z with
  | mk center multiplicity h_mult_pos =>
      simp [gammaZero]

theorem tauZero_sigmaZero_commute (z : IsolatedZeroData) :
    tauZero (sigmaZero z) = sigmaZero (tauZero z) := by
  cases z with
  | mk center multiplicity h_mult_pos =>
      simp [tauZero, sigmaZero]

theorem gammaZero_eq_tauZero_sigmaZero (z : IsolatedZeroData) :
    gammaZero z = tauZero (sigmaZero z) := by
  cases z with
  | mk center multiplicity h_mult_pos =>
      rfl

theorem zetaLogDerivativeV4_zero_action_packet (z : IsolatedZeroData) :
    tauZero (tauZero z) = z ∧
    sigmaZero (sigmaZero z) = z ∧
    gammaZero (gammaZero z) = z ∧
    tauZero (sigmaZero z) = sigmaZero (tauZero z) ∧
    gammaZero z = tauZero (sigmaZero z) := by
  exact ⟨tauZero_involutive z,
    sigmaZero_involutive z,
    gammaZero_involutive z,
    tauZero_sigmaZero_commute z,
    gammaZero_eq_tauZero_sigmaZero z⟩

end InfoGeometry.Canonical.ZetaLogDerivativeV4ZeroActionBridge
