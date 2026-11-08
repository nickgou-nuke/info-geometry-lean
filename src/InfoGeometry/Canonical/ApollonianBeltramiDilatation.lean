import Mathlib.Analysis.Complex.Trigonometric
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Scalar Beltrami/squeezing identity

This owner formalizes only the exact real scalar relation used by the
quasiconformal analogy.  It does not assert that an arbitrary Bogoliubov
transformation is a Beltrami solution or that a physical metric has already
been constructed.
-/

namespace InfoGeometry.Canonical.ApollonianBeltramiDilatation

noncomputable section

open Real

/-- The squeezing coefficient associated with a real parameter. -/
def squeezingCoefficient (r : ℝ) : ℝ := Real.tanh r

/-- The maximal-dilatation expression on the regular real domain. -/
def maximalDilatation (μ : ℝ) : ℝ := (1 + μ) / (1 - μ)

theorem squeezingCoefficient_abs_lt_one (r : ℝ) :
    |squeezingCoefficient r| < 1 := by
  exact Real.abs_tanh_lt_one r

theorem squeezingCoefficient_denominator_pos (r : ℝ) :
    0 < 1 - squeezingCoefficient r := by
  unfold squeezingCoefficient
  linarith [Real.tanh_lt_one r]

/-- The exact scalar bridge between squeezing and maximal dilatation. -/
theorem maximalDilatation_squeezingCoefficient (r : ℝ) :
    maximalDilatation (squeezingCoefficient r) = Real.exp (2 * r) := by
  unfold maximalDilatation squeezingCoefficient
  rw [Real.tanh_eq]
  have hpos : 0 < Real.exp r := Real.exp_pos r
  have hne : Real.exp r + Real.exp (-r) ≠ 0 := by
    positivity
  rw [Real.exp_neg]
  field_simp [hne]
  rw [show (2 * r : ℝ) = r + r by ring, Real.exp_add]
  ring

theorem maximalDilatation_squeezingCoefficient_pos (r : ℝ) :
    0 < maximalDilatation (squeezingCoefficient r) := by
  rw [maximalDilatation_squeezingCoefficient]
  positivity

end

end InfoGeometry.Canonical.ApollonianBeltramiDilatation
