import InfoGeometry.Krein.KreinAdjointCommutantBridge

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinCurvatureHilbertizationBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace
open InfoGeometry.Krein.KreinAdjointCommutantBridge

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [KreinSpace H]

/-- On the fundamental-symmetry commutant, Krein skew-adjointness is exactly
ordinary Hilbert skew-adjointness.

This is the native Hilbertization step needed before attaching an oriented
Pfaffian/Euler density to a Krein curvature operator. -/
theorem kreinSkewAdjoint_iff_adjoint_eq_neg_of_commutes
    (A : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A) :
    IsKreinSkewAdjoint A ↔ ContinuousLinearMap.adjoint A = -A := by
  rw [IsKreinSkewAdjoint]
  rw [kreinAdjoint_eq_adjoint_of_adjoint_commutes A
    (adjoint_commutes_of_commutes A hA)]

/-- A Krein-skew operator commuting with the fundamental symmetry is
Hilbert-skew-adjoint. -/
theorem adjoint_eq_neg_of_kreinSkewAdjoint_of_commutes
    (A : H →L[ℝ] H)
    (hAcomm : CommutesWithFundamentalSymmetry A)
    (hAskew : IsKreinSkewAdjoint A) :
    ContinuousLinearMap.adjoint A = -A :=
  (kreinSkewAdjoint_iff_adjoint_eq_neg_of_commutes A hAcomm).mp hAskew

/-- Conversely, on the fundamental-symmetry commutant an ordinary
Hilbert-skew-adjoint operator is Krein-skew-adjoint. -/
theorem kreinSkewAdjoint_of_adjoint_eq_neg_of_commutes
    (A : H →L[ℝ] H)
    (hAcomm : CommutesWithFundamentalSymmetry A)
    (hAskew : ContinuousLinearMap.adjoint A = -A) :
    IsKreinSkewAdjoint A :=
  (kreinSkewAdjoint_iff_adjoint_eq_neg_of_commutes A hAcomm).mpr hAskew

/-- The commutator of two fundamental-symmetry-compatible Krein-self-adjoint
operators is simultaneously in the Krein commutant and Hilbert-skew-adjoint.

This is the curvature-algebra form used by the Hestenes--Krein corridor:
commutator curvature can be transported to an ordinary oriented skew operator
without changing the underlying carrier. -/
theorem commutator_commutes_and_adjoint_eq_neg
    (A B : H →L[ℝ] H)
    (hAcomm : CommutesWithFundamentalSymmetry A)
    (hBcomm : CommutesWithFundamentalSymmetry B)
    (hAself : IsKreinSelfAdjoint A)
    (hBself : IsKreinSelfAdjoint B) :
    CommutesWithFundamentalSymmetry (A * B - B * A) ∧
      ContinuousLinearMap.adjoint (A * B - B * A) = -(A * B - B * A) := by
  have hcomm : CommutesWithFundamentalSymmetry (A * B - B * A) :=
    finiteKreinCommutant_commutator A B hAcomm hBcomm
  have hskew : IsKreinSkewAdjoint (A * B - B * A) :=
    finiteKreinCommutant_commutator_skewAdjoint A B hAself hBself
  exact ⟨hcomm,
    adjoint_eq_neg_of_kreinSkewAdjoint_of_commutes
      (A * B - B * A) hcomm hskew⟩

/-- The commutator curvature of two compatible Krein-self-adjoint generators
is a genuine Hilbert skew-adjoint operator. -/
theorem commutator_adjoint_eq_neg
    (A B : H →L[ℝ] H)
    (hAcomm : CommutesWithFundamentalSymmetry A)
    (hBcomm : CommutesWithFundamentalSymmetry B)
    (hAself : IsKreinSelfAdjoint A)
    (hBself : IsKreinSelfAdjoint B) :
    ContinuousLinearMap.adjoint (A * B - B * A) = -(A * B - B * A) :=
  (commutator_commutes_and_adjoint_eq_neg A B hAcomm hBcomm hAself hBself).2

end InfoGeometry.Canonical.HestenesKreinCurvatureHilbertizationBridge
