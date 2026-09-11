import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthFour

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2Combinatorics

noncomputable def canonicalResidualLengthFourEquiv :
    CanonicalResidualExponent .s1s2s1s2 ≃ (Fin 4 → Bool) := by
  have hcard : Fintype.card (CanonicalResidualExponent .s1s2s1s2) =
      Fintype.card (Fin 4 → Bool) := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthFour_card :
    Fintype.card (CanonicalResidualExponent .s1s2s1s2) = 16 := by
  rw [canonicalResidualExponent_card]
  decide

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthFour
