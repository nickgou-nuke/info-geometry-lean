import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyBoundaryTopological
import InfoGeometry.Topology.CayleyModularBoundary

namespace InfoGeometry.Canonical

open InfoGeometry.Topology

/-! Continuity statements for the Cayley chart and its pole-restricted boost. -/

theorem continuous_diskBoostParameter :
    Continuous diskBoostParameter := by
  unfold diskBoostParameter
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro s
    exact diskBoostParameter_den_ne_zero s

theorem continuous_cayleyBoundary :
    Continuous cayleyBoundary := by
  unfold cayleyBoundary
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact cayleyBoundary_den_ne_zero x

theorem continuousOn_diskBoundaryBoost (s : ℝ) :
    ContinuousOn (diskBoundaryBoost s) (diskBoundaryBoostDomain s) := by
  unfold diskBoundaryBoost
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    exact hz

theorem continuousWithinAt_diskBoundaryBoost_cayley_image
    (s : ℝ) (x : ℝ)
    (hden : (diskBoostParameter s : ℂ) * cayleyBoundary x + 1 ≠ 0) :
    ContinuousWithinAt (diskBoundaryBoost s) (diskBoundaryBoostDomain s)
      (cayleyBoundary x) :=
  continuousOn_diskBoundaryBoost s (cayleyBoundary x)
    (cayleyBoundary_image_mem_diskBoundaryBoostDomain s x hden)

end InfoGeometry.Canonical
