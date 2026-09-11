import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open TopologicalSpace
open Topology
open Set

/-- A simple closed curve in R^2 parameterized by the unit interval. -/
structure SimpleClosedCurve where
  gamma : ℝ → ℝ × ℝ
  continuous : Continuous gamma
  closed : gamma 0 = gamma 1
  simple : ∀ x y, x ∈ Ico (0 : ℝ) 1 → y ∈ Ico (0 : ℝ) 1 → x ≠ y → gamma x ≠ gamma y

/-- Definition of orientation via parameterization derivatives. -/
def IsPositivelyOrientedAt (c : SimpleClosedCurve) (t : ℝ) (deriv : ℝ × ℝ) : Prop :=
  HasDerivAt c.gamma deriv t ∧ 
  (c.gamma t).1 * deriv.2 - (c.gamma t).2 * deriv.1 > 0
