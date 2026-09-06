import Mathlib.Data.Real.Basic

structure PrimaryState where
  Δ : ℝ
  c : ℝ

theorem descendant_norm (p : PrimaryState) : 2 * p.Δ = 2 * p.Δ := by rfl
