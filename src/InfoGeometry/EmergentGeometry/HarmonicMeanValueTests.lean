import InfoGeometry.EmergentGeometry.HarmonicMeanValue

open InfoGeometry.EmergentGeometry.HarmonicMeanValue
open InnerProductSpace Metric Real

example (function : ℂ → ℝ) (center : ℂ) (radius : ℝ)
    (harmonic : HarmonicOnNhd function (closedBall center |radius|)) :
    circleAverage function center radius = function center :=
  HarmonicOnNhd.circleAverage_eq harmonic

example (function : ℂ → ℝ) (center : ℂ) (radius : ℝ)
    (harmonic : HarmonicOnNhd function (closedBall center |radius|))
    (boundary : ∀ point ∈ sphere center |radius|, function point = 0) :
    function center = 0 :=
  center_eq_of_constant_boundary harmonic 0 boundary

example (center : ℂ) (radius : ℝ) :
    ∃ function : ℂ → ℝ, HarmonicOnNhd function (closedBall center |radius|) ∧
      function center ≠ 0 :=
  harmonicity_does_not_force_zero_center center radius

#print axioms HarmonicOnNhd.circleAverage_eq
#print axioms circleIntegrable_of_harmonic
#print axioms center_eq_of_constant_boundary
#print axioms center_le_of_boundary_le
#print axioms center_comparison
#print axioms harmonicity_does_not_force_zero_center
