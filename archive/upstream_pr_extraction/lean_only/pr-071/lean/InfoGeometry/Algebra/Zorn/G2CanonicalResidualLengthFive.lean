import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthFive

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2Combinatorics

noncomputable def canonicalResidualLengthFiveEquiv :
    CanonicalResidualExponent .s1s2s1s2s1 ≃ (Fin 5 → Bool) := by
  have hcard : Fintype.card (CanonicalResidualExponent .s1s2s1s2s1) =
      Fintype.card (Fin 5 → Bool) := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthFive_card :
    Fintype.card (CanonicalResidualExponent .s1s2s1s2s1) = 32 := by
  rw [canonicalResidualExponent_card]
  decide

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthFive
