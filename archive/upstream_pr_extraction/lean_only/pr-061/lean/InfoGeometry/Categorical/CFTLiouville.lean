import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem liouville_bound (c P : ℝ) : (c - 1) / 24 + P^2 ≥ (c - 1) / 24 := by
  nlinarith
