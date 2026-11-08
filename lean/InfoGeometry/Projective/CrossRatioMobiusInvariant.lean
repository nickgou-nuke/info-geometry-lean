/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.MobiusGauge

namespace InfoGeometry.Projective

variable {K : Type*} [Field K]

/-- A fractional-linear transformation preserves the projective cross-ratio.

The hypotheses state exactly that the four affine evaluations are defined and
that the two denominators occurring in the source cross-ratio are nonzero.
The proof is the finite field identity behind Möbius covariance; no topology
or projective completion is used.
-/
theorem crossRatio_projectiveAction_invariant
    (T : MobiusMap K) (a b c d : K)
    (ha : leftGauge T a ≠ 0) (hb : leftGauge T b ≠ 0)
    (hc : leftGauge T c ≠ 0) (hd : leftGauge T d ≠ 0)
    (hac : a - c ≠ 0) (hbd : b - d ≠ 0) :
    crossRatio (projectiveAction T a) (projectiveAction T b)
        (projectiveAction T c) (projectiveAction T d) =
      crossRatio a b c d := by
  unfold crossRatio
  rw [projectiveAction_sub T a b ha hb,
    projectiveAction_sub T c d hc hd,
    projectiveAction_sub T a c ha hc,
    projectiveAction_sub T b d hb hd]
  field_simp [hac, hbd, T.det_ne_zero]

end InfoGeometry.Projective
