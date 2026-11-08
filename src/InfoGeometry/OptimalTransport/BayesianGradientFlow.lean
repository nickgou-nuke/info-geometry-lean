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

end InfoGeometry.OptimalTransport
