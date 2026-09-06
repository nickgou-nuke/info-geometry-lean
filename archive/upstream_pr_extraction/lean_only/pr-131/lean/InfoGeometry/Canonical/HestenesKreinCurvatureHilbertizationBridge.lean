import InfoGeometry.Krein.KreinAdjointCommutantBridge

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinCurvatureHilbertizationBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace
open InfoGeometry.Krein.KreinAdjointCommutantBridge

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [KreinSpace H]

theorem kreinSkewAdjoint_iff_adjoint_eq_neg_of_commutes
    (A : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A) :
    IsKreinSkewAdjoint A ↔ ContinuousLinearMap.adjoint A = -A := by
  rw [IsKreinSkewAdjoint]
  rw [kreinAdjoint_eq_adjoint_of_adjoint_commutes A
    (adjoint_commutes_of_commutes A hA)]

theorem adjoint_eq_neg_of_kreinSkewAdjoint_of_commutes
    (A : H →L[ℝ] H)
    (hAcomm : CommutesWithFundamentalSymmetry A)
    (hAskew : IsKreinSkewAdjoint A) :
    ContinuousLinearMap.adjoint A = -A :=
  (kreinSkewAdjoint_iff_adjoint_eq_neg_of_commutes A hAcomm).mp hAskew

theorem kreinSkewAdjoint_of_adjoint_eq_neg_of_commutes
    (A : H →L[ℝ] H)
    (hAcomm : CommutesWithFundamentalSymmetry A)
    (hAskew : ContinuousLinearMap.adjoint A = -A) :
    IsKreinSkewAdjoint A :=
  (kreinSkewAdjoint_iff_adjoint_eq_neg_of_commutes A hAcomm).mpr hAskew

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

theorem commutator_adjoint_eq_neg
    (A B : H →L[ℝ] H)
    (hAcomm : CommutesWithFundamentalSymmetry A)
    (hBcomm : CommutesWithFundamentalSymmetry B)
    (hAself : IsKreinSelfAdjoint A)
    (hBself : IsKreinSelfAdjoint B) :
    ContinuousLinearMap.adjoint (A * B - B * A) = -(A * B - B * A) :=
  (commutator_commutes_and_adjoint_eq_neg A B hAcomm hBcomm hAself hBself).2

end InfoGeometry.Canonical.HestenesKreinCurvatureHilbertizationBridge
