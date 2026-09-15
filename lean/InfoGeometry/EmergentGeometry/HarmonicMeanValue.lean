import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

namespace InfoGeometry.EmergentGeometry.HarmonicMeanValue

open InnerProductSpace Metric Real

variable {function comparison : ℂ → ℝ} {center : ℂ} {radius : ℝ}

theorem circleAverage_radius_invariant (firstRadius secondRadius : ℝ)
    (first_harmonic : HarmonicOnNhd function (closedBall center |firstRadius|))
    (second_harmonic : HarmonicOnNhd function (closedBall center |secondRadius|)) :
    circleAverage function center firstRadius = circleAverage function center secondRadius := by
  rw [HarmonicOnNhd.circleAverage_eq first_harmonic,
    HarmonicOnNhd.circleAverage_eq second_harmonic]

theorem circleIntegrable_of_harmonic
    (harmonic : HarmonicOnNhd function (closedBall center |radius|)) :
    CircleIntegrable function center radius := by
  apply ContinuousOn.circleIntegrable'
  intro point on_sphere
  exact (harmonic point (sphere_subset_closedBall on_sphere)).1.continuousAt.continuousWithinAt

theorem center_eq_of_constant_boundary
    (harmonic : HarmonicOnNhd function (closedBall center |radius|)) (value : ℝ)
    (boundary : ∀ point ∈ sphere center |radius|, function point = value) :
    function center = value := by
  rw [← HarmonicOnNhd.circleAverage_eq harmonic]
  exact circleAverage_const_on_circle boundary

theorem center_le_of_boundary_le
    (harmonic : HarmonicOnNhd function (closedBall center |radius|)) (bound : ℝ)
    (boundary : ∀ point ∈ sphere center |radius|, function point ≤ bound) :
    function center ≤ bound := by
  rw [← HarmonicOnNhd.circleAverage_eq harmonic]
  exact circleAverage_mono_on_of_le_circle (circleIntegrable_of_harmonic harmonic) boundary

theorem center_comparison
    (harmonic : HarmonicOnNhd function (closedBall center |radius|))
    (comparison_harmonic : HarmonicOnNhd comparison (closedBall center |radius|))
    (boundary : ∀ point ∈ sphere center |radius|, function point ≤ comparison point) :
    function center ≤ comparison center := by
  rw [← HarmonicOnNhd.circleAverage_eq harmonic, ← HarmonicOnNhd.circleAverage_eq comparison_harmonic]
  exact circleAverage_mono (circleIntegrable_of_harmonic harmonic)
    (circleIntegrable_of_harmonic comparison_harmonic) boundary

theorem harmonicity_does_not_force_zero_center (center : ℂ) (radius : ℝ) :
    ∃ function : ℂ → ℝ, HarmonicOnNhd function (closedBall center |radius|) ∧
      function center ≠ 0 := by
  refine ⟨fun _ => 1, ?_, one_ne_zero⟩
  intro point _
  simpa using (show AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) point from analyticAt_const).harmonicAt_re

end InfoGeometry.EmergentGeometry.HarmonicMeanValue
