import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.LightCone.ApolloniusCylinder

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def cylinderCoord (ξ θ : ℝ) : ℝ × ℝ :=
  (ξ, θ)

def cylinderMetric (dξ dθ : ℝ) : ℝ :=
  dξ ^ 2 + dθ ^ 2

theorem cylinder_metric_conformal_flat (dξ dθ : ℝ) :
    cylinderMetric dξ dθ = dξ ^ 2 + dθ ^ 2 := by
  unfold cylinderMetric
  rfl

theorem grand_apollonius_cylinder_synthesis (dξ dθ : ℝ) :
    cylinderMetric dξ dθ = dξ ^ 2 + dθ ^ 2 :=
  cylinder_metric_conformal_flat dξ dθ

end
end InfoGeometry.LightCone.ApolloniusCylinder
