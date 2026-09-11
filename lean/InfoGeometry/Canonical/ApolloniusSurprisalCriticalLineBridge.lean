import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

theorem apolloniusRadialNegativeLog_eq_zero_iff_criticalLine
    (ξ θ : ℝ)
    (hsum :
      (apolloniusRay ξ θ).1 + (apolloniusRay ξ θ).2 ≠ 0) :
    apolloniusRadialNegativeLog ξ θ = 0 ↔
      OnCriticalLine (projectiveS (apolloniusRay ξ θ)) := by
  rw [apolloniusRadialNegativeLog_eq_zero_iff]
  exact xi_zero_iff_projectiveS_apolloniusRay_criticalLine ξ θ hsum

theorem criticalLine_iff_apolloniusRadialNegativeLog_eq_zero
    (ξ θ : ℝ)
    (hsum :
      (apolloniusRay ξ θ).1 + (apolloniusRay ξ θ).2 ≠ 0) :
    OnCriticalLine (projectiveS (apolloniusRay ξ θ)) ↔
      apolloniusRadialNegativeLog ξ θ = 0 :=
  (apolloniusRadialNegativeLog_eq_zero_iff_criticalLine ξ θ hsum).symm

@[simp] theorem apolloniusRadialNegativeLog_zero_scale (θ : ℝ) :
    apolloniusRadialNegativeLog 0 θ = 0 := by
  rw [apolloniusRadialNegativeLog_eq]
  ring

theorem apolloniusRadialNegativeLog_cayleyInversion
    (ξ θ : ℝ) :
    apolloniusRadialNegativeLog (-ξ) (-θ) =
      -apolloniusRadialNegativeLog ξ θ := by
  rw [apolloniusRadialNegativeLog_eq,
    apolloniusRadialNegativeLog_eq]
  ring

theorem apolloniusRadialNegativeLog_pos_iff
    (ξ θ : ℝ) :
    0 < apolloniusRadialNegativeLog ξ θ ↔ ξ < 0 := by
  rw [apolloniusRadialNegativeLog_eq]
  constructor <;> intro h <;> linarith

theorem apolloniusRadialNegativeLog_neg_iff
    (ξ θ : ℝ) :
    apolloniusRadialNegativeLog ξ θ < 0 ↔ 0 < ξ := by
  rw [apolloniusRadialNegativeLog_eq]
  constructor <;> intro h <;> linarith

end InfoGeometry.Canonical.ApolloniusSurprisalCriticalLineBridge
