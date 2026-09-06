import InfoGeometry.Canonical.PrimitiveExactness

noncomputable section

open InfoGeometry.Canonical.PrimitiveExactness

#check differentiableOn_ball_to_isExactOn
#check differentiableOn_ball_exists_primitive
#check primitiveExactOn_to_zeroRectangularHolonomyOn
#check primitiveExactOn_to_analyticAt
#check primitiveExactOn_to_cauchyAnalyticAt
#check primitiveExactOn_to_doubled_cauchyAnalyticAt
#check differentiableOn_ball_to_doubled_cauchyAnalyticAt

example {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    Complex.IsExactOn f (Metric.ball c r) :=
  differentiableOn_ball_to_isExactOn hf

example {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hz : z ∈ Metric.ball c r) :
    InfoGeometry.Geometry.BilingualAnalyticity.CauchyAnalyticAt
      InfoGeometry.Canonical.ComplexAnalyticBridge.doubledPhaseStructure
      InfoGeometry.Canonical.ComplexAnalyticBridge.doubledPhaseStructure
      (InfoGeometry.Canonical.ComplexAnalyticBridge.lifted f)
      (InfoGeometry.Canonical.ComplexAnalyticBridge.complexToDoubled z) :=
  differentiableOn_ball_to_doubled_cauchyAnalyticAt hf hz
