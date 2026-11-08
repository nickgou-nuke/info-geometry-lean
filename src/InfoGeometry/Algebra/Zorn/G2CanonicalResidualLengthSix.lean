import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthSix

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2Combinatorics

noncomputable def canonicalResidualLengthSixEquiv :
    CanonicalResidualExponent .w0 ≃ (Fin 6 → Bool) := by
  have hcard : Fintype.card (CanonicalResidualExponent .w0) =
      Fintype.card (Fin 6 → Bool) := by
    rw [canonicalResidualExponent_card]
    decide
  exact (Fintype.equivFin _).trans
    ((finCongr hcard).trans (Fintype.equivFin _).symm)

theorem canonicalResidualLengthSix_card :
    Fintype.card (CanonicalResidualExponent .w0) = 64 := by
  rw [canonicalResidualExponent_card]
  decide

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualLengthSix
