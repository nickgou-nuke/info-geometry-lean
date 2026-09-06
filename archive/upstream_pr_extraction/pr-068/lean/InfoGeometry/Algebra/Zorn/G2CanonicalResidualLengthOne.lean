import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthOne

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2Combinatorics

noncomputable def canonicalResidualLengthOneEquiv :
    CanonicalResidualExponent .s1 ≃ Bool := by
  have hcard : Fintype.card (CanonicalResidualExponent .s1) = Fintype.card Bool := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthOne_card :
    Fintype.card (CanonicalResidualExponent .s1) = 2 := by
  rw [canonicalResidualExponent_card]
  decide

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthOne
