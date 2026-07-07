import Mathlib.Data.Real.Basic

/-- An unproven conjecture represented as a compiling definition. -/
theorem riemann_hypothesis : ∀ (s : ℂ), RiemannZeta s = 0 → s.re = 1/2 ∨ ∃ (n : ℤ), s = -2 * n := by
  sorry