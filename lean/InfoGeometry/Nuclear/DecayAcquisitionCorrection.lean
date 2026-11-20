/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Nuclear.DetectorBeerLambert

/-!
# Exact finite-acquisition correction for an exponential count-rate model

The expected peak counts are an actual interval integral. `referenceRate`
already includes the photon yield and detector response; it is not an activity
inferred without calibration. The live fraction is assumed constant during
the real acquisition interval. A variable live gate requires its own weighted
integral and cannot be recovered from total live and real times alone.

The integral is evaluated by reusing the existing
`DetectorBeerLambert.partialCollisionIntegral_eq` theorem. The zero-decay case
is handled explicitly. Neither daughter equilibrium nor retention is inferred.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DecayAcquisitionCorrection

open MeasureTheory

/-- Weighted exposure for a specified live gate during real acquisition time. -/
def weightedExposure (lambda realTime : ℝ) (liveGate : ℝ → ℝ) : ℝ :=
  ∫ t in 0..realTime, liveGate t * Real.exp (-lambda * t)

/-- Constant-live-fraction model of expected peak counts. -/
def expectedCounts (referenceRate lambda elapsed realTime liveTime : ℝ) : ℝ :=
  (liveTime / realTime) *
    ∫ t in 0..realTime, referenceRate * Real.exp (-lambda * (elapsed + t))

/-- The chosen acquisition model is exactly a constant live gate. -/
theorem expectedCounts_eq_weightedExposure
    (referenceRate lambda elapsed realTime liveTime : ℝ) :
    expectedCounts referenceRate lambda elapsed realTime liveTime =
      referenceRate * Real.exp (-lambda * elapsed) *
        weightedExposure lambda realTime (fun _ => liveTime / realTime) := by
  have hfun : (fun t : ℝ => referenceRate * Real.exp (-lambda * (elapsed + t))) =
      (fun t => (referenceRate * Real.exp (-lambda * elapsed)) *
        Real.exp (-lambda * t)) := by
    funext t
    rw [show -lambda * (elapsed + t) = -lambda * elapsed + -lambda * t by ring,
      Real.exp_add]
    ring
  rw [expectedCounts, hfun, intervalIntegral.integral_const_mul,
    weightedExposure, intervalIntegral.integral_const_mul]
  ring

/-- Exact integral, obtained from the existing first-collision integral owner. -/
theorem expectedCounts_eq (referenceRate lambda elapsed realTime liveTime : ℝ)
    (hlambda : lambda ≠ 0) :
    expectedCounts referenceRate lambda elapsed realTime liveTime =
      (liveTime / realTime) * Real.exp (-lambda * elapsed) *
        (referenceRate / lambda) * (1 - Real.exp (-lambda * realTime)) := by
  have hfun : (fun t : ℝ => referenceRate * Real.exp (-lambda * (elapsed + t))) =
      (fun t => Real.exp (-lambda * elapsed) *
        (referenceRate * Real.exp (-lambda * t))) := by
    funext t
    rw [show -lambda * (elapsed + t) = -lambda * elapsed + -lambda * t by ring,
      Real.exp_add]
    ring
  rw [expectedCounts, hfun, intervalIntegral.integral_const_mul,
    DetectorBeerLambert.partialCollisionIntegral_eq lambda referenceRate realTime hlambda]
  ring

/-- The no-decay model reduces to rate times live time. -/
theorem expectedCounts_zero_rate (referenceRate elapsed realTime liveTime : ℝ)
    (hreal : realTime ≠ 0) :
    expectedCounts referenceRate 0 elapsed realTime liveTime =
      referenceRate * liveTime := by
  simp [expectedCounts]
  field_simp

/-- Finite-acquisition correction, with the no-decay value defined explicitly. -/
def acquisitionFactor (lambda realTime : ℝ) : ℝ :=
  if lambda * realTime = 0 then 1
  else lambda * realTime / (1 - Real.exp (-lambda * realTime))

@[simp] theorem acquisitionFactor_zero_rate (realTime : ℝ) :
    acquisitionFactor 0 realTime = 1 := by
  simp [acquisitionFactor]

theorem one_sub_exp_neg_pos {lambda realTime : ℝ}
    (hlambda : 0 < lambda) (hreal : 0 < realTime) :
    0 < 1 - Real.exp (-lambda * realTime) := by
  have hexp : Real.exp (-lambda * realTime) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

theorem acquisitionFactor_pos {lambda realTime : ℝ}
    (hlambda : 0 < lambda) (hreal : 0 < realTime) :
    0 < acquisitionFactor lambda realTime := by
  rw [acquisitionFactor, ite_eq_right (ne_of_gt (mul_pos hlambda hreal))]
  exact div_pos (mul_pos hlambda hreal) (one_sub_exp_neg_pos hlambda hreal)

/-- For nonnegative rates, finite-acquisition correction cannot lower the
start-time-corrected rate, because its multiplicative factor is at least one. -/
theorem one_le_acquisitionFactor {lambda realTime : ℝ}
    (hlambda : 0 < lambda) (hreal : 0 < realTime) :
    1 ≤ acquisitionFactor lambda realTime := by
  rw [acquisitionFactor, ite_eq_right (ne_of_gt (mul_pos hlambda hreal))]
  apply (le_div_iff₀ (one_sub_exp_neg_pos hlambda hreal)).mpr
  have hexp := Real.add_one_le_exp (-lambda * realTime)
  nlinarith

/-- Recover the reference peak rate, under the stated acquisition model. -/
def recoverReferenceRate (counts lambda elapsed realTime liveTime : ℝ) : ℝ :=
  (counts / liveTime) * Real.exp (lambda * elapsed) * acquisitionFactor lambda realTime

/-- Exact inversion of the integrated model for positive loss and durations. -/
theorem recover_expectedCounts_pos
    (referenceRate elapsed : ℝ) {lambda realTime liveTime : ℝ}
    (hlambda : 0 < lambda) (hreal : 0 < realTime) (hlive : 0 < liveTime) :
    recoverReferenceRate
      (expectedCounts referenceRate lambda elapsed realTime liveTime)
      lambda elapsed realTime liveTime = referenceRate := by
  have hlambda0 := ne_of_gt hlambda
  have hreal0 := ne_of_gt hreal
  have hlive0 := ne_of_gt hlive
  have hden := ne_of_gt (one_sub_exp_neg_pos hlambda hreal)
  have hden' : 1 - Real.exp (-(realTime * lambda)) ≠ 0 := by
    rw [show -(realTime * lambda) = -lambda * realTime by ring]
    exact hden
  rw [recoverReferenceRate, expectedCounts_eq _ _ _ _ _ hlambda0,
    acquisitionFactor, ite_eq_right (mul_ne_zero hlambda0 hreal0)]
  rw [show -lambda * elapsed = -(lambda * elapsed) by ring, Real.exp_neg]
  have hexp := Real.exp_ne_zero (lambda * elapsed)
  field_simp [hden']

/-- Zero decay is inverted with factor one, without dividing by a zero loss rate. -/
theorem recover_expectedCounts_zero
    (referenceRate elapsed realTime liveTime : ℝ)
    (hreal : realTime ≠ 0) (hlive : liveTime ≠ 0) :
    recoverReferenceRate
      (expectedCounts referenceRate 0 elapsed realTime liveTime)
      0 elapsed realTime liveTime = referenceRate := by
  rw [recoverReferenceRate, expectedCounts_zero_rate _ _ _ _ hreal]
  simp [hlive]

/-- The physical nonnegative-loss regime, including zero loss. -/
theorem recover_expectedCounts
    (referenceRate elapsed : ℝ) {lambda realTime liveTime : ℝ}
    (hlambda : 0 ≤ lambda) (hreal : 0 < realTime) (hlive : 0 < liveTime) :
    recoverReferenceRate
      (expectedCounts referenceRate lambda elapsed realTime liveTime)
      lambda elapsed realTime liveTime = referenceRate := by
  rcases eq_or_lt_of_le hlambda with hzero | hpos
  · subst lambda
    exact recover_expectedCounts_zero _ _ _ _ (ne_of_gt hreal) (ne_of_gt hlive)
  · exact recover_expectedCounts_pos referenceRate elapsed hpos hreal hlive

end InfoGeometry.Nuclear.DecayAcquisitionCorrection
