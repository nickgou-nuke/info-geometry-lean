/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGeometry.ChiralAnomalyRobertsonBridge
import InfoGeometry.QuantumGeometry.Projective.TomitaOperatorQGTSoldering

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
open InfoGeometry.QuantumGeometry.Projective.TomitaOperatorQGTSoldering
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinCarrier
open InfoGeometry.Krein
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

/-! ### Real doubled Hestenes–Krein readout -/

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
  [CompleteSpace H₀]

local instance baseRealInner : InnerProductSpace ℝ H₀ :=
  InnerProductSpace.complexToReal

local instance doubledRealInner : InnerProductSpace ℝ (DoubledSpace H₀) :=
  InnerProductSpace.complexToReal

local notation "NambuH₀" => DoubledSpace H₀
local notation "EndNambu" => NambuH₀ →L[ℂ] NambuH₀

/-- On the doubled chiral carrier, the positive Hestenes–Krein core pairing
with the phase-rotated horizontal tangent reads the nilpotent-pair anomaly
expectation. This composes the real Krein-to-projective-QGT soldering with
the anomaly/QGT identity; it assumes the state polarization and preservation
of that polarization by the first tangent generator. -/
theorem chiralKrein_phase_readout_eq_anomaly_expectation
    (ψ : NormalizedState NambuH₀) (N : EndNambu)
    (h_nil : N * N = 0)
    (hψ : IsPositiveClockPolarized ψ.vec)
    (h_phase : CommutesClock (Complex.I • Phi N)) :
    (↑((chiralHestenesKreinSpace (E := H₀)).inducedInnerProductCore.inner
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis (E := H₀)
        (projOrth ψ (Complex.I • Phi N)))
      (projOrth ψ (J N)) : ℝ) : ℂ) =
      inner ℂ ψ.vec (Sigma N ψ.vec) := by
  calc
    _ = ((QGT ψ (Complex.I • Phi N) (J N)).im : ℂ) := by
      exact congrArg Complex.ofReal
        (chiralKreinCore_phase_inner_eq_QGT_im ψ (Complex.I • Phi N) (J N)
          hψ h_phase)
    _ = inner ℂ ψ.vec (Sigma N ψ.vec) :=
      chiral_QGT_im_eq_anomaly_expectation N h_nil ψ

end InfoGeometry.QuantumGeometry.ChiralAnomalyQGTComponentBridge
