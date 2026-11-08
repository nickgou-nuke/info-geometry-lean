import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic deformation coordinates

This owner keeps the continuous deformation scale separate from the Boolean
Koszul sign used by the supergraded product.  It records only the elementary
algebra of the exponential coordinate; KMS states, modular flows, and
state/product transport require additional hypotheses and are intentionally
owned elsewhere.
-/

noncomputable section

namespace InfoGeometry.Algebra.LogarithmicDeformationCoordinate

/-- The multiplicative activity coordinate associated to a generator and a
nonzero deformation scale.  The definition itself does not require the scale
to be positive; positivity is exposed by the corresponding theorem. -/
def activity (generator scale : ℝ) : ℝ :=
  Real.exp (generator / scale)

/-- A positive deformation scale. -/
def PositiveScale (scale : ℝ) : Prop := 0 < scale

theorem activity_pos (generator scale : ℝ) :
    0 < activity generator scale := by
  exact Real.exp_pos _

theorem activity_ne_zero (generator scale : ℝ) :
    activity generator scale ≠ 0 := by
  exact ne_of_gt (activity_pos generator scale)

theorem activity_zero (scale : ℝ) :
    activity 0 scale = 1 := by
  simp [activity]

theorem activity_add (x y scale : ℝ) :
    activity (x + y) scale = activity x scale * activity y scale := by
  simp [activity, add_div, Real.exp_add]

theorem log_activity (generator scale : ℝ) :
    Real.log (activity generator scale) = generator / scale := by
  exact Real.log_exp _

theorem positiveScale_ne_zero {scale : ℝ} (hscale : PositiveScale scale) :
    scale ≠ 0 := ne_of_gt hscale

end InfoGeometry.Algebra.LogarithmicDeformationCoordinate
