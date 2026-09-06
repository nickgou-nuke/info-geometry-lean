import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthTwo

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2Combinatorics

noncomputable def canonicalResidualLengthTwoEquiv :
    CanonicalResidualExponent .s1s2 ≃ (Fin 2 → Bool) := by
  have hcard : Fintype.card (CanonicalResidualExponent .s1s2) =
      Fintype.card (Fin 2 → Bool) := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthTwo_card :
    Fintype.card (CanonicalResidualExponent .s1s2) = 4 := by
  rw [canonicalResidualExponent_card]
  decide

noncomputable def canonicalResidualLengthTwoOppositeEquiv :
    CanonicalResidualExponent .s2s1 ≃ (Fin 2 → Bool) := by
  have hcard : Fintype.card (CanonicalResidualExponent .s2s1) =
      Fintype.card (Fin 2 → Bool) := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthTwoOpposite_card :
    Fintype.card (CanonicalResidualExponent .s2s1) = 4 := by
  rw [canonicalResidualExponent_card]
  decide

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthTwo
