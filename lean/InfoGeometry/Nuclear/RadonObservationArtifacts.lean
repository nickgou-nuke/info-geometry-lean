/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Nuclear.RadonDiffusionProfiles
import InfoGeometry.Nuclear.DecayAcquisitionCorrection
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Transport profiles, additive backgrounds, and handling loss

A constant offset in a measured count rate is an observation-model term.
Adding the same constant to a homogeneous diffusion–decay solution instead
changes its differential-equation residual by `-lambda * background`.
The proofs use actual derivatives and preserve both regularity hypotheses.

The remaining identities describe separate sources of non-identifiability:
signal/background decompositions and temporal loss correlated with position.
They do not infer that leakage, humidity, or background caused an observed
endpoint deviation. Clock differences are not disassembly or sealing times.
-/

noncomputable section

namespace InfoGeometry.Nuclear.RadonObservationArtifacts

open InfoGeometry.Nuclear.RadonDiffusionProfiles
open InfoGeometry.Nuclear.DecayAcquisitionCorrection

/-- A spatially constant offset, used here to test its differential equation. -/
def withConstantOffset (C : ℝ → ℝ) (background : ℝ) : ℝ → ℝ :=
  fun x => C x + background

theorem deriv_withConstantOffset (C : ℝ → ℝ) (background : ℝ)
    (hC : Differentiable ℝ C) :
    deriv (withConstantOffset C background) = deriv C := by
  funext x
  exact ((hC x).hasDerivAt.add_const background).deriv

/-- The constant offset contributes a distributed residual, not a boundary term. -/
theorem constantOffset_residual (D lambda background x : ℝ) (C : ℝ → ℝ)
    (hC : Differentiable ℝ C) :
    D * deriv (deriv (withConstantOffset C background)) x -
        lambda * withConstantOffset C background x =
      (D * deriv (deriv C) x - lambda * C x) - lambda * background := by
  rw [deriv_withConstantOffset C background hC]
  unfold withConstantOffset
  ring

/-- A homogeneous solution plus a constant solves the same homogeneous equation
exactly when the loss rate times that constant is zero. -/
theorem constantOffset_solves_iff (D lambda background : ℝ) (C : ℝ → ℝ)
    (hC : SolvesDiffusionDecay D lambda C) :
    SolvesDiffusionDecay D lambda (withConstantOffset C background) ↔
      lambda * background = 0 := by
  constructor
  · intro h
    have hx := h.2.2 0
    rw [constantOffset_residual D lambda background 0 C hC.1, hC.2.2 0] at hx
    linarith
  · intro hzero
    refine ⟨hC.1.add (differentiable_const background), ?_, ?_⟩
    · rw [deriv_withConstantOffset C background hC.1]
      exact hC.2.1
    · intro x
      rw [constantOffset_residual D lambda background x C hC.1, hC.2.2 x, hzero]
      ring

theorem constantOffset_not_solves (D lambda background : ℝ) (C : ℝ → ℝ)
    (hC : SolvesDiffusionDecay D lambda C)
    (hlambda : lambda ≠ 0) (hbackground : background ≠ 0) :
    ¬ SolvesDiffusionDecay D lambda (withConstantOffset C background) := by
  rw [constantOffset_solves_iff D lambda background C hC]
  exact mul_ne_zero hlambda hbackground

/-- The offset is compatible with a constant source term `lambda * background`. -/
theorem constantOffset_source_balance (D lambda background x : ℝ) (C : ℝ → ℝ)
    (hC : SolvesDiffusionDecay D lambda C) :
    D * deriv (deriv (withConstantOffset C background)) x -
        lambda * withConstantOffset C background x + lambda * background = 0 := by
  rw [constantOffset_residual D lambda background x C hC.1, hC.2.2 x]
  ring

/-- Linear detector response with an additive count-rate background. -/
def affineObservation (response activity background : ℝ) : ℝ :=
  response * activity + background

/-- A free background and a free signal level cannot be separated from one
observation alone; this is an exact invariance of the observation map. -/
theorem affineObservation_shift (response activity background shift : ℝ) :
    affineObservation response (activity + shift) (background - response * shift) =
      affineObservation response activity background := by
  unfold affineObservation
  ring

/-- A two-peak mixture ratio, including the response and background of each line. -/
def mixtureRatio (activity response₁ response₂ background₁ background₂ : ℝ) : ℝ :=
  affineObservation response₁ activity background₁ /
    affineObservation response₂ activity background₂

/-- The mixture equals the detector-response ratio exactly when its two background
components are proportional to the signal responses. No equilibrium is inferred. -/
theorem mixtureRatio_eq_response_ratio_iff
    (activity response₁ response₂ background₁ background₂ : ℝ)
    (hresponse : response₂ ≠ 0)
    (hden : affineObservation response₂ activity background₂ ≠ 0) :
    mixtureRatio activity response₁ response₂ background₁ background₂ =
        response₁ / response₂ ↔
      response₂ * background₁ = response₁ * background₂ := by
  rw [mixtureRatio, div_eq_div_iff hden hresponse]
  unfold affineObservation
  constructor <;> intro h <;> nlinarith

/-- Applying a decay correction to a stationary background multiplies that
background by the same reference-time factor. -/
theorem pointCorrection_background (signal background lambda elapsed : ℝ) :
    (signal + background) * Real.exp (lambda * elapsed) =
      signal * Real.exp (lambda * elapsed) +
      background * Real.exp (lambda * elapsed) := by
  ring

/-- Integrated decaying signal plus a stationary background per unit live time. -/
def countsWithBackground (referenceRate lambda elapsed realTime liveTime background : ℝ) : ℝ :=
  expectedCounts referenceRate lambda elapsed realTime liveTime + background * liveTime

/-- Subtract the specified stationary background before applying the integrated
decay inverse. The background value is model input, not estimated by this theorem. -/
theorem recover_background_subtracted
    (referenceRate elapsed background : ℝ) {lambda realTime liveTime : ℝ}
    (hlambda : 0 ≤ lambda) (hreal : 0 < realTime) (hlive : 0 < liveTime) :
    recoverReferenceRate
      (countsWithBackground referenceRate lambda elapsed realTime liveTime background -
        background * liveTime) lambda elapsed realTime liveTime = referenceRate := by
  unfold countsWithBackground
  rw [add_sub_cancel_right]
  exact recover_expectedCounts referenceRate elapsed hlambda hreal hlive

/-- A spatial exponential subjected to additional exponential handling loss. -/
def lossyObservation (amplitude attenuation lossRate elapsed position : ℝ) : ℝ :=
  amplitude * Real.exp (-attenuation * position) * Real.exp (-lossRate * elapsed)

/-- If elapsed time is affine in position, temporal loss changes the observed
amplitude and slope. The actual recorded times need not be exactly affine. -/
theorem lossyObservation_affine_clock
    (amplitude attenuation lossRate timeOrigin timeSlope position : ℝ) :
    lossyObservation amplitude attenuation lossRate
        (timeOrigin + timeSlope * position) position =
      (amplitude * Real.exp (-lossRate * timeOrigin)) *
        Real.exp (-(attenuation + lossRate * timeSlope) * position) := by
  unfold lossyObservation
  rw [show -lossRate * (timeOrigin + timeSlope * position) =
      -lossRate * timeOrigin + (-lossRate * timeSlope) * position by ring,
    Real.exp_add]
  rw [show -(attenuation + lossRate * timeSlope) * position =
      -attenuation * position + (-lossRate * timeSlope) * position by ring,
    Real.exp_add]
  ring

end InfoGeometry.Nuclear.RadonObservationArtifacts
