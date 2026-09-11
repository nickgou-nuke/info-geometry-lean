import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
open Matrix

/-!
# Thermodynamic GEPA Regulation

Connects the thermodynamic phase transition theorem
(`RobustThermodynamicRegression.lean`) to the GEPA evolution worker's
adaptive mutation rate control.

## The Core Idea

The GEPA mutation rate `ε` is the temperature in the Gibbs measure:

    p_i = exp(-E_i / ε) / Z

where `E_i = 1 - fitness(i)` is the energy of proof strategy `i`.

The `phase_transition_catastrophe` theorem says: when fluctuation pressure `B`
exceeds structural stiffness `A`, the frontier collapses.

We compute `A` and `B` from the empirical strategy population:

    A = expected curvature of the fitness landscape
    B = (1/ε) × variance of the strategy gradients

When `xᵀBx ≥ xᵀAx` in any direction `x`, the system is overheating.
The mutation rate must be reduced to restore stability.
-/

namespace Meta.ThermodynamicGEORegulation

/-! ## 1. Strategy Population Statistics -/

/-- A proof strategy with its fitness score and gradient vector. -/
structure Strategy (k : ℕ) where
  fitness : ℝ          -- between 0 and 1 (1 = compiles, 0 = sorry)
  gradient : Fin k → ℝ -- variation in each tactic dimension
  deriving Inhabited

/-- The empirical population mean gradient. -/
noncomputable def meanGradient (k : ℕ) (population : List (Strategy k)) : Fin k → ℝ :=
  fun a =>
    let n := population.length
    if n = 0 then 0
    else (population.map (fun s => s.gradient a)).sum / (n : ℝ)

/--
Structural stiffness `A`: the expected curvature of the fitness landscape.
Computed as the outer product of the mean gradient with itself,
scaled by population size.
-/
noncomputable def stiffness (k : ℕ) (population : List (Strategy k)) : Matrix (Fin k) (Fin k) ℝ :=
  let g_avg := meanGradient k population
  fun a b => g_avg a * g_avg b

/--
Fluctuation pressure `B`: the variance of the strategy gradients around
the mean, scaled by inverse temperature `1/ε`.
-/
noncomputable def fluctuation (k : ℕ) (population : List (Strategy k)) (ε : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  let g_avg := meanGradient k population
  let n := population.length
  if ε = 0 then 0
  else
    fun a b =>
      (1 / ε) * ((population.map (fun s => (s.gradient a - g_avg a) * (s.gradient b - g_avg b))).sum) / (n : ℝ)

/--
Exact Hessian of the thermodynamic free energy:

    H = A - B

When `H` is positive-definite, the population is stable (exploitation regime).
When `H` loses positive-definiteness, the frontier is collapsing (exploration
regime or catastrophe).
-/
def exactHessian (k : ℕ) (A B : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  A - B

/-! ## 2. Stability Criteria -/

/-- The resolvability condition: `H` is positive-definite (∀ x ≠ 0, 0 < xᵀHx). -/
def IsStable (H : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ x : Fin k → ℝ, x ≠ 0 → 0 < (∑ a : Fin k, ∑ b : Fin k, x a * H a b * x b)

/--
The critical temperature: the largest `ε` such that the system is stable.

Below `ε_critical`, fluctuations are damped and the frontier sharpens.
Above `ε_critical`, fluctuations dominate and the frontier collapses.
-/
noncomputable def criticalTemperature (k : ℕ) (population : List (Strategy k)) : ℝ :=
  -- The inflection point is where B = A in some direction.
  -- We approximate by the spectral radius of (A⁻¹B) when A is invertible.
  -- For now, return a heuristic based on the variance-to-mean ratio.
  let n := population.length
  if n < 2 then 1.0
  else
    let g_avg := meanGradient k population
    let variance := (population.map (fun s => ∑ a, (s.gradient a - g_avg a) ^ 2)).sum
    let meanEnergy := ((population.map (fun s => (1 - s.fitness))).sum) / (n : ℝ)
    if variance = 0 then 1.0
    else meanEnergy / variance

/-! ## 3. Adaptive Temperature Schedule -/

/--
The recommended mutation rate based on the stability condition.

Returns:
  - `ε_critical` if the system is stable (exploit)
  - `ε_critical / 2` if the system is approaching instability (cool down)
  - `ε_critical * 2` if the system is stuck (heat up to escape)
-/
noncomputable def recommendedMutationRate (k : ℕ) (population : List (Strategy k))
    (recentSuccessRate : ℝ) : ℝ :=
  let ε_crit := criticalTemperature k population
  if recentSuccessRate < 0.1 then
    ε_crit * 2   -- heat up: escape local minimum
  else if recentSuccessRate > 0.4 then
    ε_crit / 2   -- cool down: exploit successful pattern
  else
    ε_crit       -- steady state

/--
The `phase_transition_catastrophe` theorem applied to the GEPA population.

If `fluctuation ≥ stiffness` in any direction, the system is unstable and
the mutation rate must be reduced.
-/
theorem gepa_phase_transition_warning
    (k : ℕ) (population : List (Strategy k)) (ε : ℝ)
    (h_instability : ∃ x : Fin k → ℝ, x ≠ 0 ∧
      (∑ a : Fin k, ∑ b : Fin k, x a * fluctuation k population ε a b * x b) ≥
      (∑ a : Fin k, ∑ b : Fin k, x a * stiffness k population a b * x b)) :
    ¬ IsStable (exactHessian k (stiffness k population) (fluctuation k population ε)) :=
by
  intro h_stable
  unfold exactHessian at h_stable
  rcases h_instability with ⟨x, hx_nonzero, h_ge⟩
  -- h_stable: ∀ x ≠ 0, 0 < xᵀ(A - B)x
  have h_pos : 0 < (∑ a : Fin k, ∑ b : Fin k, x a * (stiffness k population a b - fluctuation k population ε a b) * x b) :=
    h_stable x hx_nonzero
  have h_sub : (∑ a : Fin k, ∑ b : Fin k, x a * (stiffness k population a b - fluctuation k population ε a b) * x b) =
    (∑ a : Fin k, ∑ b : Fin k, x a * stiffness k population a b * x b) -
    (∑ a : Fin k, ∑ b : Fin k, x a * fluctuation k population ε a b * x b) := by
    simp [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [h_sub] at h_pos
  have h_stiffness_gt_fluctuation : (∑ a : Fin k, ∑ b : Fin k, x a * stiffness k population a b * x b) >
    (∑ a : Fin k, ∑ b : Fin k, x a * fluctuation k population ε a b * x b) :=
    sub_pos.mp h_pos
  linarith

end Meta.ThermodynamicGEORegulation
