import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

example (x : ℝ) : Real.cosh x * (1 / 2) + Real.sinh x * (-1 / 2) = Real.exp (-x) * (1 / 2) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring
