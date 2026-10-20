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
  have hga : T.γ * a + T.δ ≠ 0 := by simpa [leftGauge] using ha
  have hgb : T.γ * b + T.δ ≠ 0 := by simpa [leftGauge] using hb
  have hgc : T.γ * c + T.δ ≠ 0 := by simpa [leftGauge] using hc
  have hgd : T.γ * d + T.δ ≠ 0 := by simpa [leftGauge] using hd
  have hdiff (x y : K) (hx : T.γ * x + T.δ ≠ 0)
      (hy : T.γ * y + T.δ ≠ 0) :
      projectiveAction T x - projectiveAction T y =
        (T.α * T.δ - T.β * T.γ) * (x - y) /
          ((T.γ * x + T.δ) * (T.γ * y + T.δ)) := by
    unfold projectiveAction
    have hxy : (T.γ * x + T.δ) * (T.γ * y + T.δ) ≠ 0 :=
      mul_ne_zero hx hy
    have hx' : x * T.γ + T.δ ≠ 0 := by simpa [mul_comm] using hx
    have hy' : y * T.γ + T.δ ≠ 0 := by simpa [mul_comm] using hy
    field_simp [hx, hy, hxy, hx', hy']
    ring
  rw [hdiff a b hga hgb, hdiff c d hgc hgd,
    hdiff a c hga hgc, hdiff b d hgb hgd]
  field_simp [hac, hbd, T.det_ne_zero]

end InfoGeometry.Projective
