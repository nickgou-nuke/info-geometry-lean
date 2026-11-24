/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic boundary of the Bayesian gradient-flow lane

This upstream entry point is retained as a small, truthful interface.  The
analytic Wasserstein and entropy-flow theorems are not asserted here; the
reusable theorem below is the exact one-dimensional log-barrier identity.
-/

namespace InfoGeometry.OptimalTransport

noncomputable def barrierSecondDeriv (x : ℝ) : ℝ := 1 / x ^ 2

noncomputable def barrierThirdDeriv (x : ℝ) : ℝ := -2 / x ^ 3

theorem barrier_self_concordance_squared (x : ℝ) :
    (barrierThirdDeriv x) ^ 2 = 4 * (barrierSecondDeriv x) ^ 3 := by
  unfold barrierThirdDeriv barrierSecondDeriv
  ring

def WassersteinMetric (P : Type*) : Prop :=
  ∃ dist : P → P → ℝ,
    (∀ p q : P, 0 ≤ dist p q) ∧
    (∀ p : P, dist p p = 0) ∧
    (∀ p q : P, dist p q = dist q p) ∧
    (∀ p q : P, dist p q = 0 → p = q) ∧
    (∀ p q r : P, dist p r ≤ dist p q + dist q r)

/-- The rational function `1 / x²`. -/
noncomputable def BarrierSecondDeriv (x : ℝ) : ℝ :=
  1 / (x^2)

/-- The rational function `-2 / x³`. -/
noncomputable def BarrierThirdDeriv (x : ℝ) : ℝ :=
  -2 / (x^3)

/-- Squared rational identity for the two barrier functions above. -/
theorem causal_barrier_self_concordance (x : ℝ) :
  (BarrierThirdDeriv x)^2 = 4 * (BarrierSecondDeriv x)^3 := by
  unfold BarrierThirdDeriv BarrierSecondDeriv
  -- (-2 / x^3)^2 = 4 / x^6
  -- 4 * (1 / x^2)^3 = 4 / x^6
  have h1 : (-2 / x^3)^2 = 4 / x^6 := by ring
  have h2 : 4 * (1 / x^2)^3 = 4 / x^6 := by ring
  rw [h1, h2]

end InfoGeometry.OptimalTransport
