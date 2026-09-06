import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
import Mathlib.Tactic

/-!
# Local conformal-coordinate certificate for the bipolar logarithm

The phrase "the pullback metric is flat" is represented here at the exact
coordinate level rather than by introducing a parallel curvature formalism.
On every compatible principal-log chart, `W = log(s/(1-s))` is holomorphic and
has nonzero derivative

`W'(s) = 1 / (s(1-s))`.

Therefore `W` is a noncritical local conformal coordinate.  The metric density
recorded in `BipolarApolloniusReflectionMetric` is exactly `|W'|²`.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLocalConformalCoordinate

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric

/-- The branch-independent logarithmic differential never vanishes on the
punctured domain. -/
theorem dlog01_ne_zero {s : ℂ} (hs : s ∈ punctured01) : dlog01 s ≠ 0 := by
  rw [dlog01_eq_one_div_mul hs]
  exact one_div_ne_zero (mul_ne_zero hs.1 (one_sub_ne_zero_of_mem hs))

/-- The pullback metric density is strictly positive on the punctured domain. -/
theorem metricDensity_pos {s : ℂ} (hs : s ∈ punctured01) :
    0 < metricDensity s := by
  exact Complex.normSq_pos.mpr (dlog01_ne_zero hs)

/-- Local principal-log chart certificate: the derivative exists and is nonzero. -/
theorem bipolarLog_local_coordinate {s : ℂ}
    (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (dlog01 s) s ∧ dlog01 s ≠ 0 := by
  exact ⟨hasDerivAt_bipolarLog hs hslit, dlog01_ne_zero hs⟩

/-- Compact local conformal packet. -/
theorem local_conformal_packet {s : ℂ}
    (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (dlog01 s) s ∧
      dlog01 s ≠ 0 ∧
      0 < metricDensity s := by
  exact ⟨hasDerivAt_bipolarLog hs hslit,
    dlog01_ne_zero hs,
    metricDensity_pos hs⟩

end InfoGeometry.Analysis.BipolarLocalConformalCoordinate
