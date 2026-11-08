import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring

theorem cross_ratio_translation (z1 z2 z3 z4 c : ℝ) : (z1+c - (z2+c)) * (z3+c - (z4+c)) = (z1-z2)*(z3-z4) := by ring

theorem cross_ratio_scale (z1 z2 z3 z4 k : ℝ) : (k*z1 - k*z2) * (k*z3 - k*z4) = k^2 * (z1-z2)*(z3-z4) := by ring
