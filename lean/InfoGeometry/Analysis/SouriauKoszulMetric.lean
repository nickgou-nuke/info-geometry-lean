import InfoGeometry.Analysis.SouriauThermodynamics
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Analysis.SouriauKoszulMetric

Finite Souriau-Koszul metric hypotheses and debt lemmas.

The deleted version attempted to postulate a directional Hessian.
This repaired version keeps the mathematically honest part: a Hessian evaluator
is supplied as data, and the metric is the corresponding bilinear readout.
-/

namespace InfoGeometry.Analysis

/-- A supplied directional Hessian evaluator for a potential `Φ`. -/
abbrev DirectionalHessian
    (_Φ : SL2cAlgebra → ℝ) : Type :=
  SL2cAlgebra → SL2cAlgebra → SL2cAlgebra → ℝ

/-- Souriau-Koszul-Fisher metric readout from a supplied Hessian evaluator. -/
noncomputable def SKF_metric
    (Φ : SL2cAlgebra → ℝ)
    (directionalHessian : DirectionalHessian Φ)
    (β : SL2cAlgebra) : SL2cAlgebra → SL2cAlgebra → ℝ :=
  fun X Y => directionalHessian β X Y

/-- The metric readout is definitionally the supplied directional Hessian. -/
theorem SKF_metric_apply
    (Φ : SL2cAlgebra → ℝ)
    (directionalHessian : DirectionalHessian Φ)
    (β X Y : SL2cAlgebra) :
    SKF_metric Φ directionalHessian β X Y = directionalHessian β X Y := by
  rfl

end InfoGeometry.Analysis
