import InfoGeometry.Codes.MajoranaStabilizerThreshold
import InfoGeometry.Dynamics.WassersteinProximalBridge
import Mathlib.Data.Fintype.Lattice
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

/-! ## Finite variational base case -/

/-- A real-valued objective on a finite nonempty state space attains a minimum. -/
theorem finite_jko_objective_has_minimizer
    {P : Type*} [Finite P] [Nonempty P] (objective : P → ℝ) :
    ∃ p₀ : P, ∀ p : P, objective p₀ ≤ objective p := by
  exact Finite.exists_min objective

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

/-! ## Finite variational JKO certificate -/

def finiteJKOTransportCost (tau x₀ x : ℝ) : ℝ :=
  (x - x₀) ^ 2 / (2 * tau)

theorem finiteJKOTransportCost_self (tau x₀ : ℝ) :
    finiteJKOTransportCost tau x₀ x₀ = 0 := by
  simp [finiteJKOTransportCost]

theorem finiteJKOTransportCost_nonneg (tau x₀ x : ℝ) (htau : 0 < tau) :
    0 ≤ finiteJKOTransportCost tau x₀ x := by
  unfold finiteJKOTransportCost
  positivity

theorem finiteJKOTransportCost_eq_zero_iff (tau x₀ x : ℝ) (htau : 0 < tau) :
    finiteJKOTransportCost tau x₀ x = 0 ↔ x = x₀ := by
  unfold finiteJKOTransportCost
  have hden : 2 * tau ≠ 0 := by positivity
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
    · exact (hden h).elim
  · intro h
    simp [h]

theorem finiteJKOTransportCost_pos_of_ne
    (tau x₀ x : ℝ) (htau : 0 < tau) (hne : x ≠ x₀) :
    0 < finiteJKOTransportCost tau x₀ x := by
  have hnonneg := finiteJKOTransportCost_nonneg tau x₀ x htau
  have hzero : finiteJKOTransportCost tau x₀ x ≠ 0 := by
    intro hz
    exact hne ((finiteJKOTransportCost_eq_zero_iff tau x₀ x htau).mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

theorem finiteJKOTransportCost_prior_minimizer (tau x₀ x : ℝ) (htau : 0 < tau) :
    finiteJKOTransportCost tau x₀ x₀ ≤ finiteJKOTransportCost tau x₀ x := by
  rw [finiteJKOTransportCost_self tau x₀]
  unfold finiteJKOTransportCost
  positivity

theorem finiteJKOTransportCost_prior_eq_iff (tau x₀ x : ℝ) (htau : 0 < tau) :
    finiteJKOTransportCost tau x₀ x₀ = finiteJKOTransportCost tau x₀ x ↔
      x = x₀ := by
  rw [finiteJKOTransportCost_self tau x₀]
  unfold finiteJKOTransportCost
  constructor
  · intro h
    have hquot : (x - x₀) ^ 2 / (2 * tau) = 0 := by linarith
    have hden : (2 * tau) ≠ 0 := by nlinarith
    have hsq : (x - x₀) ^ 2 = 0 :=
      (div_eq_zero_iff).mp hquot |>.resolve_right hden
    nlinarith [sq_eq_zero_iff.mp hsq]
  · intro h
    simp [h]

def finiteJKOFunctional (energy : ℝ → ℝ) (tau x₀ x : ℝ) : ℝ :=
  energy x + finiteJKOTransportCost tau x₀ x

def finiteJKOArgmin (energy : ℝ → ℝ) (tau x₀ : ℝ) : Set ℝ :=
  {x | ∀ y, finiteJKOFunctional energy tau x₀ x ≤
    finiteJKOFunctional energy tau x₀ y}

theorem finiteJKOFunctional_constantEnergy_prior_minimizer
    (c : ℝ) (tau x₀ x : ℝ) (htau : 0 < tau) :
    finiteJKOFunctional (fun _ => c) tau x₀ x₀ ≤
      finiteJKOFunctional (fun _ => c) tau x₀ x := by
  dsimp [finiteJKOFunctional]
  rw [finiteJKOTransportCost_self tau x₀]
  linarith [finiteJKOTransportCost_nonneg tau x₀ x htau]

theorem finiteJKOFunctional_constantEnergy_eq_iff
    (c : ℝ) (tau x₀ x : ℝ) (htau : 0 < tau) :
    finiteJKOFunctional (fun _ => c) tau x₀ x₀ =
      finiteJKOFunctional (fun _ => c) tau x₀ x ↔ x = x₀ := by
  simpa [finiteJKOFunctional] using
    (finiteJKOTransportCost_prior_eq_iff tau x₀ x htau)

theorem finiteJKOArgmin_constantEnergy_prior_mem
    (c : ℝ) (tau x₀ : ℝ) (htau : 0 < tau) :
    x₀ ∈ finiteJKOArgmin (fun _ => c) tau x₀ := by
  intro y
  exact finiteJKOFunctional_constantEnergy_prior_minimizer c tau x₀ y htau

theorem finiteJKOArgmin_constantEnergy_eq_singleton
    (c : ℝ) (tau x₀ : ℝ) (htau : 0 < tau) :
    finiteJKOArgmin (fun _ => c) tau x₀ = {x₀} := by
  ext x
  constructor
  · intro hx
    have hle := hx x₀
    have hge := finiteJKOFunctional_constantEnergy_prior_minimizer c tau x₀ x htau
    have heq : finiteJKOFunctional (fun _ => c) tau x₀ x₀ =
        finiteJKOFunctional (fun _ => c) tau x₀ x :=
      le_antisymm hge hle
    exact (finiteJKOFunctional_constantEnergy_eq_iff c tau x₀ x htau).mp heq
  · intro hx
    have hxeq : x = x₀ := by simpa using hx
    subst x
    exact finiteJKOArgmin_constantEnergy_prior_mem c tau x₀ htau

def affineJKOFunctional (a : ℝ) (tau x₀ x : ℝ) : ℝ :=
  a * x + finiteJKOTransportCost tau x₀ x

def affineJKOProximalPoint (a tau x₀ : ℝ) : ℝ :=
  x₀ - tau * a

def affineJKOArgmin (a tau x₀ : ℝ) : Set ℝ :=
  {x | ∀ y, affineJKOFunctional a tau x₀ x ≤
    affineJKOFunctional a tau x₀ y}

theorem affineJKOProximalPoint_minimizer
    (a tau x₀ x : ℝ) (htau : 0 < tau) :
    affineJKOFunctional a tau x₀ (affineJKOProximalPoint a tau x₀) ≤
      affineJKOFunctional a tau x₀ x := by
  have hden : (2 * tau) ≠ 0 := by nlinarith
  have hsq : 0 ≤ (x - affineJKOProximalPoint a tau x₀) ^ 2 / (2 * tau) := by
    positivity
  have hidentity :
      affineJKOFunctional a tau x₀ x =
        affineJKOFunctional a tau x₀ (affineJKOProximalPoint a tau x₀) +
          (x - affineJKOProximalPoint a tau x₀) ^ 2 / (2 * tau) := by
    unfold affineJKOFunctional affineJKOProximalPoint finiteJKOTransportCost
    field_simp [hden]
    ring
  rw [hidentity]
  linarith

theorem affineJKOProximalPoint_eq_iff
    (a tau x₀ x : ℝ) (htau : 0 < tau) :
    affineJKOFunctional a tau x₀ (affineJKOProximalPoint a tau x₀) =
      affineJKOFunctional a tau x₀ x ↔
        x = affineJKOProximalPoint a tau x₀ := by
  have hden : (2 * tau) ≠ 0 := by nlinarith
  have hidentity :
      affineJKOFunctional a tau x₀ x =
        affineJKOFunctional a tau x₀ (affineJKOProximalPoint a tau x₀) +
          (x - affineJKOProximalPoint a tau x₀) ^ 2 / (2 * tau) := by
    unfold affineJKOFunctional affineJKOProximalPoint finiteJKOTransportCost
    field_simp [hden]
    ring
  constructor
  · intro h
    have hquot : (x - affineJKOProximalPoint a tau x₀) ^ 2 / (2 * tau) = 0 := by
      rw [hidentity] at h
      linarith
    have hsq : (x - affineJKOProximalPoint a tau x₀) ^ 2 = 0 := by
      rcases (div_eq_zero_iff).mp hquot with hsq | hzero
      · exact hsq
      · exact (hden hzero).elim
    nlinarith [sq_eq_zero_iff.mp hsq]
  · intro h
    simp [h]

theorem affineJKOArgmin_eq_singleton
    (a tau x₀ : ℝ) (htau : 0 < tau) :
    affineJKOArgmin a tau x₀ =
      {affineJKOProximalPoint a tau x₀} := by
  ext x
  constructor
  · intro hx
    have hle := hx (affineJKOProximalPoint a tau x₀)
    have hge := affineJKOProximalPoint_minimizer a tau x₀ x htau
    have heq : affineJKOFunctional a tau x₀ (affineJKOProximalPoint a tau x₀) =
        affineJKOFunctional a tau x₀ x :=
      le_antisymm hge hle
    exact (affineJKOProximalPoint_eq_iff a tau x₀ x htau).mp heq
  · intro hx
    have hxeq : x = affineJKOProximalPoint a tau x₀ := by simpa using hx
    subst x
    intro y
    exact affineJKOProximalPoint_minimizer a tau x₀ y htau

theorem affineJKOProximalPoint_composition
    (a tau₁ tau₂ x₀ : ℝ) :
    affineJKOProximalPoint a tau₂
        (affineJKOProximalPoint a tau₁ x₀) =
      affineJKOProximalPoint a (tau₁ + tau₂) x₀ := by
  unfold affineJKOProximalPoint
  ring

def vectorAffineJKOFunctional (a x₀ x : Fin 2 → ℝ) (tau : ℝ) : ℝ :=
  ∑ i, affineJKOFunctional (a i) tau (x₀ i) (x i)

def vectorAffineJKOProximalPoint (a x₀ : Fin 2 → ℝ) (tau : ℝ) : Fin 2 → ℝ :=
  fun i => affineJKOProximalPoint (a i) tau (x₀ i)

theorem vectorAffineJKOProximalPoint_minimizer
    (a x₀ x : Fin 2 → ℝ) (tau : ℝ) (htau : 0 < tau) :
    vectorAffineJKOFunctional a x₀ (vectorAffineJKOProximalPoint a x₀ tau) tau ≤
      vectorAffineJKOFunctional a x₀ x tau := by
  unfold vectorAffineJKOFunctional vectorAffineJKOProximalPoint
  apply Finset.sum_le_sum
  intro i hi
  exact affineJKOProximalPoint_minimizer (a i) tau (x₀ i) (x i) htau

theorem vectorAffineJKOProximalPoint_composition
    (a : Fin 2 → ℝ) (tau₁ tau₂ : ℝ) (x₀ : Fin 2 → ℝ) :
    vectorAffineJKOProximalPoint a
        (vectorAffineJKOProximalPoint a x₀ tau₁) tau₂ =
      vectorAffineJKOProximalPoint a x₀ (tau₁ + tau₂) := by
  funext i
  exact affineJKOProximalPoint_composition (a i) tau₁ tau₂ (x₀ i)

def vectorAffineJKOArgmin (a x₀ : Fin 2 → ℝ) (tau : ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∀ y, vectorAffineJKOFunctional a x₀ x tau ≤
    vectorAffineJKOFunctional a x₀ y tau}

theorem vectorAffineJKOArgmin_proximalPoint_mem
    (a x₀ : Fin 2 → ℝ) (tau : ℝ) (htau : 0 < tau) :
    vectorAffineJKOProximalPoint a x₀ tau ∈
      vectorAffineJKOArgmin a x₀ tau := by
  intro y
  exact vectorAffineJKOProximalPoint_minimizer a x₀ y tau htau

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

theorem bregman_prox_zero :
    bregmanProxStep 0 = 1 := by
  simp [bregmanProxStep, errorFlowStep, lcftParabolicFlowStep,
    infinitesimalNullGenerator,
    InfoGeometry.Clifford.LogCftMonodromy.epsilon,
    InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent]

theorem bregman_prox_mul_neg (δ : ℂ) :
    bregmanProxStep δ * bregmanProxStep (-δ) = 1 := by
  unfold bregmanProxStep
  exact lcftParabolicFlow_mul_neg δ

theorem bregman_prox_neg_mul (δ : ℂ) :
    bregmanProxStep (-δ) * bregmanProxStep δ = 1 := by
  unfold bregmanProxStep
  exact lcftParabolicFlow_neg_mul δ

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

theorem bregman_prox_pow (δ : ℂ) (n : ℕ) :
    bregmanProxStep δ ^ n = bregmanProxStep ((n : ℂ) * δ) := by
  exact bregman_prox_induction δ n

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
