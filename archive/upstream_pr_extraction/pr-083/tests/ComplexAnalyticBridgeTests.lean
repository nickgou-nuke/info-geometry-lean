import InfoGeometry.Canonical.ComplexAnalyticBridge

open InfoGeometry.Canonical.ComplexAnalyticBridge

#check analyticAt_liftedToDoubled_cauchyAnalyticAt
#check complexDoubledCLE
#check lifted
#check clockAxis_complexToDoubled

example (z : ℂ) : doubledToComplex (complexToDoubled z) = z := by
  simp

example (v : InfoGeometry.Krein.DoubledSpace ℝ) :
    complexToDoubled (doubledToComplex v) = v := by
  simp
