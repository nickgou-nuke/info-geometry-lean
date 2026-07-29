import Mathlib.Data.Real.Basic

abbrev PrimaryState := ℝ × ℝ

namespace PrimaryState

abbrev Δ (p : PrimaryState) : ℝ := p.1
abbrev c (p : PrimaryState) : ℝ := p.2

end PrimaryState

theorem descendant_norm (p : PrimaryState) : 2 * p.Δ = 2 * p.Δ := by rfl
