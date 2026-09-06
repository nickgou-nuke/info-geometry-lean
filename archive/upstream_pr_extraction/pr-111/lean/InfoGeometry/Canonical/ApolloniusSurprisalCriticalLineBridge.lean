import Mathlib.Tactic
import InfoGeometry.Canonical.NegativeLogReadoutBridge
import InfoGeometry.Canonical.ApolloniusCriticalLineLeafBridge

/-!
# Apollonius surprisal and the critical-line leaf

This file closes the exact scalar bridge between the repository's
negative-log Apollonius readout and its projective critical-line geometry.
The statement is only the elementary equivalence

`zero radial surprisal ↔ zero Apollonius scale ↔ Re(s) = 1/2`

inside the established projective chart.  It does not identify zeta zeros
with flux punctures and does not assert the Riemann hypothesis.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusSurprisalCriticalLineBridge

open Complex Real
open InfoGeometry.Projective.ApolloniusNatural
open InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.NegativeLogReadoutBridge

/-- The negative-log Apollonius readout vanishes exactly on the projective
critical-line leaf, away from the affine-chart pole. -/
theorem apolloniusRadialNegativeLog_eq_zero_iff_criticalLine
    (ξ θ : ℝ)
    (hsum :
      (apolloniusRay ξ θ).1 + (apolloniusRay ξ θ).2 ≠ 0) :
    apolloniusRadialNegativeLog ξ θ = 0 ↔
      OnCriticalLine (projectiveS (apolloniusRay ξ θ)) := by
  rw [apolloniusRadialNegativeLog_eq_zero_iff]
  exact xi_zero_iff_projectiveS_apolloniusRay_criticalLine ξ θ hsum

/-- Symmetric orientation of the zero-surprisal/critical-line equivalence. -/
theorem criticalLine_iff_apolloniusRadialNegativeLog_eq_zero
    (ξ θ : ℝ)
    (hsum :
      (apolloniusRay ξ θ).1 + (apolloniusRay ξ θ).2 ≠ 0) :
    OnCriticalLine (projectiveS (apolloniusRay ξ θ)) ↔
      apolloniusRadialNegativeLog ξ θ = 0 :=
  (apolloniusRadialNegativeLog_eq_zero_iff_criticalLine ξ θ hsum).symm

/-- The zero-scale Apollonius equator has zero negative-log readout. -/
@[simp] theorem apolloniusRadialNegativeLog_zero_scale (θ : ℝ) :
    apolloniusRadialNegativeLog 0 θ = 0 := by
  rw [apolloniusRadialNegativeLog_eq]
  ring

/-- Cayley inversion in natural coordinates reverses the radial
negative-log potential.  The angular sign is included because
`exp(ξ + iθ)⁻¹ = exp(-ξ - iθ)`. -/
theorem apolloniusRadialNegativeLog_cayleyInversion
    (ξ θ : ℝ) :
    apolloniusRadialNegativeLog (-ξ) (-θ) =
      -apolloniusRadialNegativeLog ξ θ := by
  rw [apolloniusRadialNegativeLog_eq,
    apolloniusRadialNegativeLog_eq]
  ring

/-- The sign of the negative-log readout records the side of the zero-scale
leaf: it is positive precisely for negative radial coordinate. -/
theorem apolloniusRadialNegativeLog_pos_iff
    (ξ θ : ℝ) :
    0 < apolloniusRadialNegativeLog ξ θ ↔ ξ < 0 := by
  rw [apolloniusRadialNegativeLog_eq]
  constructor <;> intro h <;> linarith

/-- The negative-log readout is negative precisely for positive radial
coordinate. -/
theorem apolloniusRadialNegativeLog_neg_iff
    (ξ θ : ℝ) :
    apolloniusRadialNegativeLog ξ θ < 0 ↔ 0 < ξ := by
  rw [apolloniusRadialNegativeLog_eq]
  constructor <;> intro h <;> linarith

end InfoGeometry.Canonical.ApolloniusSurprisalCriticalLineBridge
