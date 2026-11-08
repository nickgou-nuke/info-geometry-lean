/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.CrossRatioMobiusInvariant

namespace InfoGeometry.Projective

variable {K : Type*} [Field K]

/-- Exact covariance of the affine chart under a fractional-linear action.

The chart is not invariant by itself: it acquires the expected gauge factor
`leftGauge T zi / leftGauge T x`.  This is the finite affine statement whose
four-point cancellation gives cross-ratio invariance.
-/
theorem affineChart_projectiveAction_covariant
    (T : MobiusMap K) (zi zk x : K)
    (hzi : leftGauge T zi ≠ 0) (hzk : leftGauge T zk ≠ 0)
    (hx : leftGauge T x ≠ 0) (hik : zi - zk ≠ 0) :
    ((projectiveAction T x - projectiveAction T zk) /
        (projectiveAction T zi - projectiveAction T zk)) =
      ((x - zk) / (zi - zk)) *
        ((leftGauge T zi) / (leftGauge T x)) := by
  have hzi' : T.γ * zi + T.δ ≠ 0 := by simpa [leftGauge] using hzi
  have hzk' : T.γ * zk + T.δ ≠ 0 := by simpa [leftGauge] using hzk
  have hx' : T.γ * x + T.δ ≠ 0 := by simpa [leftGauge] using hx
  rw [projectiveAction_sub T x zk hx hzk,
    projectiveAction_sub T zi zk hzi hzk]
  unfold leftGauge
  field_simp [hik, hzi', hzk', hx', T.det_ne_zero]

end InfoGeometry.Projective
