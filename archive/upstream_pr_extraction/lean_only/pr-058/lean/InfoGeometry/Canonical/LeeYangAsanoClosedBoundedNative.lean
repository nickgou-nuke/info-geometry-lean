import InfoGeometry.Canonical.LeeYangAsanoDigest
import InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint
import InfoGeometry.Analysis.AsanoContractionNative

/-!
# Native closed-and-bounded Asano--Ruelle source theorem

This owner is downstream of the theorem-shape digest.  It proves the
corrected source claim from the actual finite pole argument.  The unrestricted
claim remains separate and is known to be false; no endpoint alternative is
accepted as a premise here.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoClosedBoundedNative

open InfoGeometry.Canonical.LeeYangAsanoDigest
open InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint

open scoped BigOperators

/--
The finite closed-and-bounded Asano--Ruelle contraction theorem.

The proof splits on `D = 0` and `AD - BC = 0`.  In the remaining branch the
endpoint disjunction is obtained from closedness, boundedness, origin
avoidance, and zero-freeness by the canonical pole theorem.
-/
theorem source_claim_closed_bounded_native :
    AsanoRuelleLemmaSourceClaimClosedBounded := by
  intro K1 K2 P h0K1 h0K2 hClosed1 hClosed2 hBdd1 hBdd2 hPhi z hzOff
  have hzf :
      InfoGeometry.Analysis.AsanoContractionNative.ZeroFreeOutside
        K1 K2 P.A P.B P.C P.D := by
    intro z1 z2 hz1 hz2
    simpa
      [InfoGeometry.Analysis.AsanoContractionNative.ZeroFreeOutside,
       InfoGeometry.Analysis.AsanoContractionNative.asanoPoly,
       TwoVarAffinePolynomial.eval]
      using hPhi z1 z2 hz1 hz2
  have hzOff' :
      z ∉ InfoGeometry.Analysis.AsanoContractionNative.signedProductSet K1 K2 := by
    simpa [InfoGeometry.Analysis.AsanoContractionNative.signedProductSet,
      asanoForbiddenSet] using hzOff
  by_cases hD : P.D = 0
  · exact InfoGeometry.Analysis.AsanoContractionNative.asanoContract_ne_zero_of_D_eq_zero
      h0K1 h0K2 hzf hD
  · by_cases hdet : P.A * P.D - P.B * P.C = 0
    · exact InfoGeometry.Analysis.AsanoContractionNative.asanoContract_ne_zero_outside_signedProduct_of_rankOne
        h0K1 h0K2 hzf hD hdet hzOff'
    · have hend :
          (P.C ≠ 0 ∧ -(P.C / P.D) ∈ K1) ∨
            (P.B ≠ 0 ∧ -(P.B / P.D) ∈ K2) :=
        by
          simpa [neg_div] using
            asano_endpoint_disjunction_combined
              P.A P.B P.C P.D K1 K2 hD hdet hClosed1 hClosed2
              (Or.inr hBdd2) h0K1 h0K2 hzf
      have hne :=
        InfoGeometry.Analysis.AsanoContractionNative.asanoContract_ne_zero_outside_signedProduct_of_endpoint_nonDeg
          h0K1 h0K2 hzf
          (fun _ _ => hend) hzOff'
      simpa [TwoVarAffinePolynomial.contract,
        InfoGeometry.Analysis.AsanoContractionNative.asanoContract] using hne

end InfoGeometry.Canonical.LeeYangAsanoClosedBoundedNative
