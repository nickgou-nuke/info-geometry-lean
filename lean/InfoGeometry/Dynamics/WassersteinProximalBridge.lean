import InfoGeometry.Codes.MajoranaStabilizerThreshold
import InfoGeometry.Clifford.MonodromyFlowAdapter
import Mathlib.Analysis.Complex.Basic

noncomputable section

/-!
# WassersteinProximalBridge

Discrete proximal-flow readout for the same parabolic nilpotent update used by
the LCFT monodromy and Majorana threshold modules.

This file does not formalize the full analytic JKO theorem or the heat equation.
It provides the finite-dimensional envelope used by that analogy: a constant
step-size proximal update is represented by the unipotent matrix
`[[1, η], [0, 1]]`, so `n` iterations are exactly one update with parameter
`n * η`.
-/

namespace WassersteinProximalBridge

open Matrix
open Complex
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.MonodromyFlowAdapter
open InfoGeometry.Codes.MajoranaStabilizerThreshold

/-- A simplified two-coordinate Gaussian envelope, e.g. location plus covariance profile. -/
abbrev GaussianStateEnvelope := Fin 2 → ℂ

/--
JKO-style entropy step in the finite parabolic envelope.  The parameter `η`
plays the role of the discrete time step / learning rate.
-/
def jkoEntropyStep (η : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  errorFlowStep η

/-- A covariance-envelope step uses the heat-flow convention `variance += 2t`. -/
def gaussianHeatEnvelopeStep (η : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  jkoEntropyStep (2 * η)

/-- The JKO-style proximal steps compose additively in their time parameters. -/
theorem jkoEntropyStep_composition (η₁ η₂ : ℂ) :
    jkoEntropyStep η₁ * jkoEntropyStep η₂ = jkoEntropyStep (η₁ + η₂) := by
  exact errorFlow_composition η₁ η₂

/--
Executing `n` constant JKO-style steps with parameter `η` is the same as one
parabolic update with accumulated time `(n : ℂ) * η`.
-/
theorem jko_flow_stability_induction (η : ℂ) (n : ℕ) :
    jkoEntropyStep η ^ n = errorFlowStep ((n : ℂ) * η) := by
  exact error_threshold_linear_induction η n

/-- The off-diagonal update entry records total discrete optimization time. -/
theorem jko_accumulated_step (η : ℂ) (n : ℕ) :
    ((jkoEntropyStep η) ^ n) 0 1 = (n : ℂ) * η := by
  exact majorana_accumulated_shear η n

/--
For the Gaussian heat-envelope convention, variance time accumulates as
`2 * n * η`.
-/
theorem gaussianHeatEnvelope_accumulated_variance_step (η : ℂ) (n : ℕ) :
    ((gaussianHeatEnvelopeStep η) ^ n) 0 1 = (n : ℂ) * (2 * η) := by
  exact jko_accumulated_step (2 * η) n

/--
LCFT monodromy is the same parabolic optimizer envelope at the imaginary step
`logShearBase`, up to the global conformal phase.
-/
theorem monodromy_is_wasserstein_optimizer (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n • jkoEntropyStep ((n : ℂ) * logShearBase) := by
  simpa [jkoEntropyStep, errorFlowStep] using
    monodromy_pow_is_compounded_flow h n

/-- The same deterministic norm budget controls the proximal envelope. -/
theorem optimizer_threshold_bound (η : ℂ) (n : ℕ) (Λ : ℝ)
    (h_budget : (n : ℝ) * ‖η‖ ≤ Λ) :
    ‖(((jkoEntropyStep η) ^ n) 0 1)‖ ≤ Λ := by
  exact threshold_condition η n Λ h_budget

/-- Real drift in the optimization envelope is linear in the iteration count. -/
theorem optimizer_real_drift_is_linear (η : ℂ) (n : ℕ) :
    (((jkoEntropyStep η) ^ n) 0 1).re = (n : ℝ) * η.re := by
  exact dephasing_drift_is_linear η n

end WassersteinProximalBridge
