import InfoGeometry.Codes.MajoranaStabilizerThreshold
import InfoGeometry.Clifford.MonodromyFlowAdapter
import InfoGeometry.Physics.LogCFTJordanShear
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

namespace InfoGeometry.Dynamics.WassersteinProximalBridge

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

theorem jkoEntropyStep_eq_logCFTJordanShear (η : ℂ) :
    jkoEntropyStep η =
      InfoGeometry.Physics.LogCFTJordanShear.unipotentShear η := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jkoEntropyStep, errorFlowStep, lcftParabolicFlowStep,
      infinitesimalNullGenerator,
      InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent,
      InfoGeometry.Physics.LogCFTJordanShear.unipotentShear,
      InfoGeometry.Physics.LogCFTJordanShear.nilpotentN,
      InfoGeometry.Clifford.LogCftMonodromy.epsilon,
      Matrix.add_apply]

theorem jkoEntropyStep_eq_exp (η : ℂ) :
    jkoEntropyStep η =
      NormedSpace.exp (η • infinitesimalNullGenerator) := by
  have hN : infinitesimalNullGenerator =
      InfoGeometry.Physics.LogCFTJordanShear.nilpotentN := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [infinitesimalNullGenerator,
        InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent,
        InfoGeometry.Physics.LogCFTJordanShear.nilpotentN]
  rw [hN, InfoGeometry.Physics.LogCFTJordanShear.exp_scaledNilpotent]
  exact jkoEntropyStep_eq_logCFTJordanShear η

/-- A covariance-envelope step uses the heat-flow convention `variance += 2t`. -/
def gaussianHeatEnvelopeStep (η : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  jkoEntropyStep (2 * η)

theorem gaussianHeatEnvelopeStep_zero :
    gaussianHeatEnvelopeStep 0 = 1 := by
  unfold gaussianHeatEnvelopeStep
  rw [jkoEntropyStep_eq_logCFTJordanShear]
  simp [InfoGeometry.Physics.LogCFTJordanShear.unipotentShear]

theorem gaussianHeatEnvelopeStep_eq_exp (η : ℂ) :
    gaussianHeatEnvelopeStep η =
      NormedSpace.exp ((2 * η) • infinitesimalNullGenerator) := by
  unfold gaussianHeatEnvelopeStep
  exact jkoEntropyStep_eq_exp (2 * η)

theorem gaussianHeatEnvelopeStep_composition (η₁ η₂ : ℂ) :
    gaussianHeatEnvelopeStep η₁ * gaussianHeatEnvelopeStep η₂ =
      gaussianHeatEnvelopeStep (η₁ + η₂) := by
  change errorFlowStep (2 * η₁) * errorFlowStep (2 * η₂) =
    errorFlowStep (2 * (η₁ + η₂))
  rw [errorFlow_composition]
  congr 1
  ring

/-- The JKO-style proximal steps compose additively in their time parameters. -/
theorem jkoEntropyStep_composition (η₁ η₂ : ℂ) :
    jkoEntropyStep η₁ * jkoEntropyStep η₂ = jkoEntropyStep (η₁ + η₂) := by
  exact errorFlow_composition η₁ η₂

theorem jkoEntropyStep_zero :
    jkoEntropyStep 0 = 1 := by
  simp [jkoEntropyStep, errorFlowStep, lcftParabolicFlowStep,
    infinitesimalNullGenerator,
    InfoGeometry.Clifford.LogCftMonodromy.epsilon,
    InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent]

theorem jkoEntropyStep_mul_neg (η : ℂ) :
    jkoEntropyStep η * jkoEntropyStep (-η) = 1 := by
  unfold jkoEntropyStep
  exact lcftParabolicFlow_mul_neg η

theorem jkoEntropyStep_neg_mul (η : ℂ) :
    jkoEntropyStep (-η) * jkoEntropyStep η = 1 := by
  unfold jkoEntropyStep
  exact lcftParabolicFlow_neg_mul η

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

theorem gaussianHeatEnvelope_flow_stability (η : ℂ) (n : ℕ) :
    gaussianHeatEnvelopeStep η ^ n =
      errorFlowStep ((n : ℂ) * (2 * η)) := by
  exact jko_flow_stability_induction (2 * η) n

theorem gaussianHeatEnvelope_pow (η : ℂ) (n : ℕ) :
    gaussianHeatEnvelopeStep η ^ n =
      gaussianHeatEnvelopeStep ((n : ℂ) * η) := by
  unfold gaussianHeatEnvelopeStep
  rw [jkoEntropyStep_eq_logCFTJordanShear,
    jkoEntropyStep_eq_logCFTJordanShear]
  convert
    (InfoGeometry.Physics.LogCFTJordanShear.unipotentShear_pow_eq
      (2 * η) n) using 1
  ring_nf

theorem gaussianHeatEnvelopeStep_mul_neg (η : ℂ) :
    gaussianHeatEnvelopeStep η * gaussianHeatEnvelopeStep (-η) = 1 := by
  unfold gaussianHeatEnvelopeStep
  rw [jkoEntropyStep_eq_logCFTJordanShear,
    jkoEntropyStep_eq_logCFTJordanShear]
  simpa using
    (InfoGeometry.Physics.LogCFTJordanShear.unipotentShear_mul_neg (2 * η))

theorem gaussianHeatEnvelopeStep_neg_mul (η : ℂ) :
    gaussianHeatEnvelopeStep (-η) * gaussianHeatEnvelopeStep η = 1 := by
  unfold gaussianHeatEnvelopeStep
  rw [jkoEntropyStep_eq_logCFTJordanShear,
    jkoEntropyStep_eq_logCFTJordanShear]
  simpa using
    (InfoGeometry.Physics.LogCFTJordanShear.unipotentShear_neg_mul (2 * η))

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

end InfoGeometry.Dynamics.WassersteinProximalBridge
