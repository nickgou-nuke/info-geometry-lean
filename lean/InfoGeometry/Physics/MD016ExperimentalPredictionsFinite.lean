import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Repaired MD 016: finite experimental-prediction algebra

Source: `github-nick:nickgou-nuke/MD`, file `016.md`.

Chapter 16 presents quantitative experimental predictions: high-energy
cross-section modifications, triality/neutrino-mixing hypotheses, gravitational
wave dispersion, Planck-scale corrections, dark-energy entropy models, and
cosmological parameter fits.  The physical predictions depend on hypotheses,
phenomenological constants, QFT amplitudes, PDE dispersion analysis, detector
models, and cosmological dynamics that are not finite algebraic theorems.

This owner formalizes only the finite scalar algebra appearing in the displayed
prediction formulae:

* the cross-section modification factor and its zero-coupling/zero-energy limits;
* the finite linearized triality-breaking angle shadow;
* the frequency-quadratic gravitational-wave speed shadow and its deficit;
* the entropy-scaling equation-of-state shadow `w = -1 + ε/3`;
* a two-component flat cosmology ratio model whose components sum to one.

No theorem here asserts collider amplitudes, neutrino mixing predictions, CP
violation, gravitational-wave PDEs, Lorentz-violation bounds, dark-energy
physics, Planck-2018 parameter derivations, or experimental detectability.
-/

noncomputable section

namespace InfoGeometry.Physics.MD016ExperimentalPredictionsFinite

/-- Finite scalar cross-section modification factor `1 + α E²/Λ² F`. -/
def crossSectionFactor (alpha E Lambda angular : ℝ) : ℝ :=
  1 + alpha * E ^ 2 / Lambda ^ 2 * angular

/-- Modified scalar cross-section shadow. -/
def modifiedCrossSection (sigmaSM alpha E Lambda angular : ℝ) : ℝ :=
  sigmaSM * crossSectionFactor alpha E Lambda angular

/-- Zero new coupling gives no finite cross-section modification. -/
theorem crossSectionFactor_zero_alpha (E Lambda angular : ℝ) :
    crossSectionFactor 0 E Lambda angular = 1 := by
  simp [crossSectionFactor]

/-- Zero energy gives no finite cross-section modification. -/
theorem crossSectionFactor_zero_energy (alpha Lambda angular : ℝ) :
    crossSectionFactor alpha 0 Lambda angular = 1 := by
  simp [crossSectionFactor]

/-- The excess over the Standard-Model scalar is the displayed correction term. -/
theorem modifiedCrossSection_excess
    (sigmaSM alpha E Lambda angular : ℝ) :
    modifiedCrossSection sigmaSM alpha E Lambda angular - sigmaSM =
      sigmaSM * (alpha * E ^ 2 / Lambda ^ 2 * angular) := by
  unfold modifiedCrossSection crossSectionFactor
  ring

/-- Finite linearized triality-breaking angle shadow. -/
def linearTrialityAngleShift (baseline sensitivity delta : ℝ) : ℝ :=
  baseline + sensitivity * delta

/-- No breaking parameter leaves the baseline angle shadow unchanged. -/
theorem linearTrialityAngleShift_zero_delta (baseline sensitivity : ℝ) :
    linearTrialityAngleShift baseline sensitivity 0 = baseline := by
  simp [linearTrialityAngleShift]

/-- Difference from the baseline is the linear triality-breaking term. -/
theorem linearTrialityAngleShift_sub_baseline (baseline sensitivity delta : ℝ) :
    linearTrialityAngleShift baseline sensitivity delta - baseline = sensitivity * delta := by
  unfold linearTrialityAngleShift
  ring

/-- Frequency-quadratic gravitational-wave speed shadow `c(1 - β(f/f₀)²)`. -/
def gwSpeedShadow (c beta f f0 : ℝ) : ℝ :=
  c * (1 - beta * (f / f0) ^ 2)

/-- At zero frequency, the finite speed shadow is the reference speed. -/
theorem gwSpeedShadow_zero_frequency (c beta f0 : ℝ) :
    gwSpeedShadow c beta 0 f0 = c := by
  simp [gwSpeedShadow]

/-- At the reference frequency, the finite speed shadow is `c(1-β)`. -/
theorem gwSpeedShadow_reference_frequency (c beta f0 : ℝ) (hf0 : f0 ≠ 0) :
    gwSpeedShadow c beta f0 f0 = c * (1 - beta) := by
  unfold gwSpeedShadow
  field_simp [hf0]

/-- The speed deficit is exactly the displayed quadratic correction. -/
theorem gwSpeedShadow_deficit (c beta f f0 : ℝ) :
    c - gwSpeedShadow c beta f f0 = c * beta * (f / f0) ^ 2 := by
  unfold gwSpeedShadow
  ring

/-- Scalar beta coefficient shadow `β = 6π² γ f₀²`. -/
def gwBetaCoeff (gamma f0 : ℝ) : ℝ :=
  6 * Real.pi ^ 2 * gamma * f0 ^ 2

/-- Zero higher-derivative coefficient gives zero finite dispersion coefficient. -/
theorem gwBetaCoeff_zero_gamma (f0 : ℝ) :
    gwBetaCoeff 0 f0 = 0 := by
  simp [gwBetaCoeff]

/-- Entropy-scaling equation-of-state shadow `w = -1 + ε/3`. -/
def darkEnergyEOS (epsilon : ℝ) : ℝ :=
  -1 + epsilon / 3

/-- No entropy-scaling correction gives the cosmological-constant value. -/
theorem darkEnergyEOS_zero : darkEnergyEOS 0 = -1 := by
  norm_num [darkEnergyEOS]

/-- The displayed sample `ε = 0.06` gives `w = -0.98` as exact rational arithmetic. -/
theorem darkEnergyEOS_sample :
    darkEnergyEOS (6 / 100 : ℝ) = -98 / 100 := by
  norm_num [darkEnergyEOS]

/-- Flat two-component cosmology ratio shadow. -/
def omegaLambdaRatio (gamma : ℝ) : ℝ :=
  1 / (1 + gamma)

/-- Complementary matter ratio shadow. -/
def omegaMatterRatio (gamma : ℝ) : ℝ :=
  gamma / (1 + gamma)

/-- The two finite ratio components sum to one when the denominator is nonzero. -/
theorem omegaRatios_sum_one (gamma : ℝ) (hgamma : 1 + gamma ≠ 0) :
    omegaLambdaRatio gamma + omegaMatterRatio gamma = 1 := by
  unfold omegaLambdaRatio omegaMatterRatio
  field_simp [hgamma]

/-- Repaired theorem-safe Chapter 16 finite prediction-algebra packet. -/
theorem repaired_MD016_prediction_packet
    (sigmaSM alpha E Lambda angular baseline sensitivity delta c beta f f0 gamma : ℝ)
    (hf0 : f0 ≠ 0) (hgamma : 1 + gamma ≠ 0) :
    modifiedCrossSection sigmaSM alpha E Lambda angular - sigmaSM =
      sigmaSM * (alpha * E ^ 2 / Lambda ^ 2 * angular) ∧
    linearTrialityAngleShift baseline sensitivity delta - baseline = sensitivity * delta ∧
    gwSpeedShadow c beta f0 f0 = c * (1 - beta) ∧
    c - gwSpeedShadow c beta f f0 = c * beta * (f / f0) ^ 2 ∧
    darkEnergyEOS (6 / 100 : ℝ) = -98 / 100 ∧
    omegaLambdaRatio gamma + omegaMatterRatio gamma = 1 := by
  exact ⟨modifiedCrossSection_excess sigmaSM alpha E Lambda angular,
    linearTrialityAngleShift_sub_baseline baseline sensitivity delta,
    gwSpeedShadow_reference_frequency c beta f0 hf0,
    gwSpeedShadow_deficit c beta f f0,
    darkEnergyEOS_sample,
    omegaRatios_sum_one gamma hgamma⟩

end InfoGeometry.Physics.MD016ExperimentalPredictionsFinite

end noncomputable section
