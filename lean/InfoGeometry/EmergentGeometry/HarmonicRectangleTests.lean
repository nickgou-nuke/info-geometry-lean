import InfoGeometry.EmergentGeometry.HarmonicRectangle

open InfoGeometry.EmergentGeometry.HarmonicRectangle

example : rectangleIntegral quadraticHarmonic 2 1 = 8 := by
  norm_num [quadraticHarmonic_rectangleIntegral]

example : rectangleIntegral quadraticHarmonic 2 1 / 8 = 1 := by
  norm_num [quadraticHarmonic_rectangleIntegral]

example (radius : ℝ) : Real.circleAverage quadraticHarmonic 0 radius = 0 :=
  quadraticHarmonic_circleAverage radius

example (halfWidth halfHeight : ℝ) (width_positive : 0 < halfWidth)
    (height_positive : 0 < halfHeight) (unequal : halfWidth ≠ halfHeight) :
    rectangleIntegral quadraticHarmonic halfWidth halfHeight /
      (4 * halfWidth * halfHeight) ≠ quadraticHarmonic 0 := by
  exact fun equality => unequal ((quadraticHarmonic_center_mean_iff_square
    halfWidth halfHeight width_positive height_positive).mp equality)

#print axioms quadraticHarmonic_harmonic
#print axioms quadraticHarmonic_coordinates
#print axioms quadraticHarmonic_vertical_integral
#print axioms quadraticHarmonic_rectangleIntegral
#print axioms quadraticHarmonic_rectangle_average
#print axioms quadraticHarmonic_center_mean_iff_square
#print axioms harmonic_rectangle_counterexample
#print axioms quadraticHarmonic_circleAverage
