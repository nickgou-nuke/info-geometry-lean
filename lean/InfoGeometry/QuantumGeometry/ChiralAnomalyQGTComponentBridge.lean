/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGeometry.ChiralAnomalyRobertsonBridge

/-!
# Complex QGT component of the chiral anomaly

The projective Hilbert-space QGT on the skew-adjoint chiral pair `(i Φ, J)`
has an imaginary component given exactly by the state expectation of the
operator anomaly `Σ`. This is a scalar Hilbert-space readout; it does not
identify an indefinite Krein form with a positive QGT.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.ChiralAnomalyQGTComponentBridge

open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.QuantumGeometry.ChiralAnomalyRobertsonBridge
open OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- The imaginary component of the projective QGT of the chiral pair
`(i Φ, J)` is the expectation of the nilpotent-pair anomaly `Σ`.

The assertion applies to every normalized state and only assumes square-zero
of `N`; regularity is needed for the separate support/idempotency results. -/
theorem chiral_QGT_im_eq_anomaly_expectation (N : EndH)
    (h_nil : N * N = 0) (ψ : NormalizedState H) :
    ((QGT ψ (Complex.I • Phi N) (J N)).im : ℂ) =
      inner ℂ ψ.vec (Sigma N ψ.vec) := by
  let q := QGT ψ (Complex.I • Phi N) (J N)
  let z := inner ℂ ψ.vec (Sigma N ψ.vec)
  have hBerry := berryCurvature_eq_neg_two_anomaly_expectation N h_nil ψ
  have hCast : (berryCurvature ψ (Complex.I • Phi N) (J N) : ℂ) =
      (-2 : ℂ) * (q.im : ℂ) := by
    change ((-2 * (QGT ψ (Complex.I • Phi N) (J N)).im : ℝ) : ℂ) = _
    simp [q, Complex.ofReal_mul]
  have hFactor : ((-2 : ℂ) * Complex.I) * ((q.im : ℂ) - z) = 0 := by
    calc ((-2 : ℂ) * Complex.I) * ((q.im : ℂ) - z)
        = (((-2 : ℂ) * (q.im : ℂ)) * Complex.I) -
            (((-2 : ℂ) * Complex.I) * z) := by ring
      _ = (berryCurvature ψ (Complex.I • Phi N) (J N) : ℂ) * Complex.I -
            (((-2 : ℂ) * Complex.I) * z) := by rw [← hCast]
      _ = 0 := by rw [hBerry]; ring
  rcases mul_eq_zero.mp hFactor with hZero | hDiff
  · norm_num at hZero
  · exact sub_eq_zero.mp hDiff

end InfoGeometry.QuantumGeometry.ChiralAnomalyQGTComponentBridge
