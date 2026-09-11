import InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib

/-!
# Endpoint carriers for the reciprocal logarithmic coordinate

This owner supplies the native extended-real carriers for the two endpoint
notations used by the reciprocal picture.  It records only endpoint names and
finite algebraic identities; it does not assert a compactification theorem or
any limit at `±∞`.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Lie.SplitOctonionCircularLogProjectiveEndpointBridge

open InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge

/-- The extended-real carrier for a logarithmic coordinate. -/
abbrev LogCompactification := EReal

/-- The logarithmic representatives of the projective triple `(0,1,∞)`. -/
def logNegativeEndpoint : LogCompactification := ⊥
def logOrigin : LogCompactification := 0
def logPositiveEndpoint : LogCompactification := ⊤

theorem logNegativeEndpoint_lt_origin :
    logNegativeEndpoint < logOrigin := by
  simp [logNegativeEndpoint, logOrigin]

theorem logOrigin_lt_positiveEndpoint :
    logOrigin < logPositiveEndpoint := by
  simp [logOrigin, logPositiveEndpoint]

theorem logNegativeEndpoint_ne_positiveEndpoint :
    logNegativeEndpoint ≠ logPositiveEndpoint := by
  simp [logNegativeEndpoint, logPositiveEndpoint]

/-- The nonnegative projective scale carrier, with endpoints `0` and `∞`. -/
abbrev PositiveProjectiveScale := ENNReal

def scaleZeroEndpoint : PositiveProjectiveScale := 0
def scaleInfinityEndpoint : PositiveProjectiveScale := ⊤

/-- The finite positive exponential coordinate in the endpoint carrier. -/
def positiveExponentialCoordinate (t : ℝ) : PositiveProjectiveScale :=
  ENNReal.ofReal (Real.exp t)

theorem positiveExponentialCoordinate_eq_reciprocalPair_fst (t : ℝ) :
    positiveExponentialCoordinate t =
      ENNReal.ofReal (reciprocalExponentialPair t).1 := rfl

theorem continuous_positiveExponentialCoordinate :
    Continuous positiveExponentialCoordinate := by
  exact ENNReal.continuous_ofReal.comp Real.continuous_exp

theorem positiveExponentialCoordinate_tendsto_atTop :
    Filter.Tendsto positiveExponentialCoordinate Filter.atTop
      (𝓝 scaleInfinityEndpoint) := by
  unfold positiveExponentialCoordinate scaleInfinityEndpoint
  exact ENNReal.tendsto_ofReal_nhds_top.mpr Real.tendsto_exp_atTop

theorem positiveExponentialCoordinate_tendsto_atBot :
    Filter.Tendsto positiveExponentialCoordinate Filter.atBot
      (𝓝 scaleZeroEndpoint) := by
  unfold positiveExponentialCoordinate scaleZeroEndpoint
  simpa only [ENNReal.ofReal_zero] using
    (ENNReal.tendsto_ofReal Real.tendsto_exp_atBot)

theorem positiveExponentialCoordinate_zero :
    positiveExponentialCoordinate 0 = 1 := by
  simp [positiveExponentialCoordinate]

theorem positiveExponentialCoordinate_ne_zero (t : ℝ) :
    positiveExponentialCoordinate t ≠ scaleZeroEndpoint := by
  simp [positiveExponentialCoordinate, scaleZeroEndpoint, Real.exp_pos]

theorem positiveExponentialCoordinate_ne_top (t : ℝ) :
    positiveExponentialCoordinate t ≠ scaleInfinityEndpoint := by
  simp [positiveExponentialCoordinate, scaleInfinityEndpoint]

theorem positiveExponentialCoordinate_mul_reciprocal (t : ℝ) :
    positiveExponentialCoordinate t *
        positiveExponentialCoordinate (-t) = 1 := by
  rw [positiveExponentialCoordinate, positiveExponentialCoordinate,
    ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos t))]
  simp [← Real.exp_add]

theorem positiveExponentialCoordinate_add (s t : ℝ) :
    positiveExponentialCoordinate (s + t) =
      positiveExponentialCoordinate s * positiveExponentialCoordinate t := by
  rw [positiveExponentialCoordinate, positiveExponentialCoordinate,
    positiveExponentialCoordinate,
    ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos s)), Real.exp_add]

end InfoGeometry.Lie.SplitOctonionCircularLogProjectiveEndpointBridge
