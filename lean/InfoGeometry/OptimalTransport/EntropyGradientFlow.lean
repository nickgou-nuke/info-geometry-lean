import InfoGeometry.Codes.MajoranaStabilizerThreshold
import InfoGeometry.Dynamics.WassersteinProximalBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

/-!
# EntropyGradientFlow

Finite-dimensional optimal-transport/Bregman readout for the parabolic
nilpotent update used by the LCFT and Majorana threshold lanes.

This module provides the convex-duality vocabulary around the already verified
matrix law.  It does not claim to formalize the full measure-theoretic JKO
scheme.  Instead, it proves the finite natural-parameter envelope:
constant Bregman/JKO-style steps add linearly, so `n` steps of size `δ` are one
step of size `n * δ`.
-/

namespace InfoGeometry.OptimalTransport.EntropyGradientFlow

open Matrix
open Complex
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.MonodromyFlowAdapter
open InfoGeometry.Codes.MajoranaStabilizerThreshold
open InfoGeometry.Dynamics.WassersteinProximalBridge

/-! ## Scalar entropy/Bregman anchors -/

/-- Natural parameter coordinate for a one-dimensional exponential-family envelope. -/
abbrev NaturalParameter := ℂ

/-- Natural generator coordinate, read as a log-Radon--Nikodym / free-energy drift. -/
abbrev NaturalGenerator := ℂ

/-- Scalar negative entropy potential on the positive-real chart. -/
def negEntropy (x : ℝ) : ℝ :=
  x * Real.log x - x

/-- Scalar KL/Bregman divergence shadow for the negative entropy potential. -/
def entropyBregmanDivergence (x y : ℝ) : ℝ :=
  negEntropy x - negEntropy y - Real.log y * (x - y)

/-- Fenchel-dual shadow of `x log x - x`, expressed in natural coordinates. -/
def entropyFenchelDual (θ : ℝ) : ℝ :=
  Real.exp θ

/-! ## Parabolic natural-parameter proximal steps -/

/--
Discrete Bregman/JKO-style proximal step in the natural-parameter envelope.
It is intentionally the same verified parabolic flow used by the code-threshold
and Wasserstein-proximal bridge modules.
-/
def bregmanProxStep (δ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  errorFlowStep δ

/-- The same step, named by the log-Radon--Nikodym generator interpretation. -/
def logRadonNikodymGeneratorStep (g : NaturalGenerator) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  bregmanProxStep g

/-- Bregman proximal steps compose by adding their generator increments. -/
theorem bregman_prox_composition (δ₁ δ₂ : ℂ) :
    bregmanProxStep δ₁ * bregmanProxStep δ₂ =
      bregmanProxStep (δ₁ + δ₂) := by
  exact errorFlow_composition δ₁ δ₂

/--
Fenchel/Bregman additive accumulation law: `n` constant generator steps equal
one step with generator `(n : ℂ) * δ`.
-/
theorem bregman_prox_induction (δ : ℂ) (n : ℕ) :
    bregmanProxStep δ ^ n = errorFlowStep ((n : ℂ) * δ) := by
  exact error_threshold_linear_induction δ n

/-- The off-diagonal entry is the accumulated natural generator. -/
theorem bregman_accumulated_generator (δ : ℂ) (n : ℕ) :
    ((bregmanProxStep δ) ^ n) 0 1 = (n : ℂ) * δ := by
  exact majorana_accumulated_shear δ n

/--
LCFT monodromy is the same Bregman natural-parameter optimizer envelope at
step `logShearBase`, up to its global conformal phase.
-/
theorem monodromy_is_bregman_optimizer (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n • bregmanProxStep ((n : ℂ) * logShearBase) := by
  simpa [bregmanProxStep, errorFlowStep] using
    monodromy_pow_is_compounded_flow h n

/-- The same deterministic norm budget controls the Bregman/free-energy envelope. -/
theorem free_energy_dissipation_bound (δ : ℂ) (n : ℕ) (Λ : ℝ)
    (h_budget : (n : ℝ) * ‖δ‖ ≤ Λ) :
    ‖(((bregmanProxStep δ) ^ n) 0 1)‖ ≤ Λ := by
  exact threshold_condition δ n Λ h_budget

/-- Real-part free-energy drift is linear in the iteration count. -/
theorem free_energy_real_drift_is_linear (δ : ℂ) (n : ℕ) :
    (((bregmanProxStep δ) ^ n) 0 1).re = (n : ℝ) * δ.re := by
  exact dephasing_drift_is_linear δ n

end InfoGeometry.OptimalTransport.EntropyGradientFlow
