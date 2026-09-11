import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false

theorem momentum_reflection (b α : ℝ) (hb : b ≠ 0) : let Q := b + b⁻¹; α * (Q - α) = (Q - α) * (Q - (Q - α)) := by
  intro Q
  ring
