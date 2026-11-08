import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.CFT.NarainTDuality

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def tDualityRadius (R : ℝ) : ℝ :=
  1 / R

def narainLeftMomentum (n w : ℤ) (R : ℝ) : ℝ :=
  (n : ℝ) / R + (w : ℝ) * R

def narainRightMomentum (n w : ℤ) (R : ℝ) : ℝ :=
  (n : ℝ) / R - (w : ℝ) * R

theorem t_duality_involution (R : ℝ) (hR : R ≠ 0) :
    tDualityRadius (tDualityRadius R) = R := by
  unfold tDualityRadius
  exact one_div_one_div R

theorem t_duality_momentum_exchange (n w : ℤ) (R : ℝ) (hR : R ≠ 0) :
    narainLeftMomentum n w (tDualityRadius R) = narainLeftMomentum w n R := by
  unfold narainLeftMomentum tDualityRadius
  field_simp [hR]
  ring
