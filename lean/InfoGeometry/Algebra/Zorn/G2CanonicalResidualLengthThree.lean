import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthThree

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2Combinatorics

noncomputable def canonicalResidualLengthThreeEquiv :
    CanonicalResidualExponent .s1s2s1 ≃ (Fin 3 → Bool) := by
  have hcard : Fintype.card (CanonicalResidualExponent .s1s2s1) =
      Fintype.card (Fin 3 → Bool) := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthThree_card :
    Fintype.card (CanonicalResidualExponent .s1s2s1) = 8 := by
  rw [canonicalResidualExponent_card]
  decide

noncomputable def canonicalResidualLengthThreeOppositeEquiv :
    CanonicalResidualExponent .s2s1s2 ≃ (Fin 3 → Bool) := by
  have hcard : Fintype.card (CanonicalResidualExponent .s2s1s2) =
      Fintype.card (Fin 3 → Bool) := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthThreeOpposite_card :
    Fintype.card (CanonicalResidualExponent .s2s1s2) = 8 := by
  rw [canonicalResidualExponent_card]
  decide

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthThree
