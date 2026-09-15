import InfoGeometry.Epistemology.QuadraticNaturalGradientFlow

open InfoGeometry.Epistemology.NaturalGradientDissipation
open InfoGeometry.Epistemology.QuadraticNaturalGradientFlow
open Filter
open scoped Topology

example (initial target time : ℝ) :
    HasDerivAt (fun instant => quadraticGeometry.divergence (trajectory initial target instant) target)
      (-dissipation quadraticGeometry (trajectory initial target time) target) time :=
  hasDerivAt_divergence_along_flow quadraticGeometry (trajectory initial target) target time
    (hasDerivAt_quadratic _).differentiableAt (hasDerivAt_trajectory initial target time)

example (initial target time : ℝ) (time_nonneg : 0 ≤ time) :
    quadraticGeometry.divergence (trajectory initial target time) target ≤
      quadraticGeometry.divergence initial target * Real.exp (-2 * time) := by
  have bound := divergence_exponential_bound quadraticGeometry (trajectory initial target)
    target 2 time (fun instant => (hasDerivAt_quadratic _).differentiableAt)
    (hasDerivAt_trajectory initial target)
    (fun instant => (quadratic_dissipation_domination _ target).ge) time_nonneg
  simpa only [trajectory_initial] using bound

example (initial target : ℝ) :
    Tendsto (fun time => quadraticGeometry.divergence (trajectory initial target time) target)
      atTop (𝓝 0) := by
  apply divergence_tendsto_zero quadraticGeometry (trajectory initial target) target 2 (by norm_num)
    (fun instant => (hasDerivAt_quadratic _).differentiableAt)
    (hasDerivAt_trajectory initial target)
    (fun instant => (quadratic_dissipation_domination _ target).ge)
  intro instant
  rw [quadratic_divergence]
  positivity

example (time : ℝ) : trajectory 1 0 time ≠ 0 :=
  trajectory_ne_target 1 0 time (by norm_num)

example (initial target time : ℝ) :
    quadraticGeometry.divergence (trajectory initial target time) target =
      quadraticGeometry.divergence initial target * Real.exp (-2 * time) :=
  divergence_exact_decay initial target time

#print axioms hasDerivAt_divergence
#print axioms hasDerivAt_divergence_along_flow
#print axioms dissipation_nonneg
#print axioms divergence_antitone
#print axioms divergence_exponential_bound
#print axioms divergence_tendsto_zero
#print axioms hasDerivAt_quadratic
#print axioms quadratic_dualMap
#print axioms quadratic_metric
#print axioms quadratic_divergence
#print axioms quadratic_naturalVelocity
#print axioms quadratic_dissipation_domination
#print axioms trajectory_initial
#print axioms hasDerivAt_trajectory
#print axioms trajectory_ne_target
#print axioms divergence_exact_decay
#print axioms trajectory_tendsto_target
