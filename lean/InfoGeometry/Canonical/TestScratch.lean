import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

example (t ω x0 x4 : ℝ) (h0 : Real.cosh (t * ω) ^ 2 - Real.sinh (t * ω) ^ 2 = 1) :
    Real.cosh (t * ω) * (Real.cosh (t * ω) * x0 - Real.sinh (t * ω) * x4) + 
    Real.sinh (t * ω) * (-(Real.sinh (t * ω) * x0) + Real.cosh (t * ω) * x4) = x0 := by
  linear_combination h0 * x0

example (t ω x0 x4 : ℝ) (h0 : Real.cosh (t * ω) ^ 2 - Real.sinh (t * ω) ^ 2 = 1) :
    Real.sinh (t * ω) * (Real.cosh (t * ω) * x0 - Real.sinh (t * ω) * x4) + 
    Real.cosh (t * ω) * (-(Real.sinh (t * ω) * x0) + Real.cosh (t * ω) * x4) = x4 := by
  linear_combination h0 * x4
