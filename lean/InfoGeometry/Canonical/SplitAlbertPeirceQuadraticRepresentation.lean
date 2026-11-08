import InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Compatibility owner for the upstream Peirce-quadratic path.  The
implementation is delegated to the current native fixed-tripoten owner. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceQuadraticRepresentation

open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev H3 := InfoGeometry.Algebra.H3Zorn ℝ
abbrev PeirceZeroCoord := InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary.PeirceZeroCoord

abbrev InPeirceZero := SplitAlbertPeirceZeroQuadraticRepresentation.InPeirceZero
abbrev U10 := SplitAlbertPeirceZeroQuadraticRepresentation.U10

theorem peirceZeroEmbed_intertwines_U10 (u v : PeirceZeroCoord) :
    SplitAlbertTripotentPeirceBoundary.peirceZeroEmbed (U10 u v) =
      InfoGeometry.Algebra.H3Zorn.U
        (SplitAlbertTripotentPeirceBoundary.peirceZeroEmbed u)
        (SplitAlbertTripotentPeirceBoundary.peirceZeroEmbed v) :=
  SplitAlbertPeirceZeroQuadraticRepresentation.peirceZeroEmbed_U10 u v

theorem U_preserves_peirceZero
    {y x : H3} (hy : InPeirceZero y) (hx : InPeirceZero x) :
    InPeirceZero (InfoGeometry.Algebra.H3Zorn.U y x) :=
  SplitAlbertPeirceZeroQuadraticRepresentation.U_preserves_peirceZero hy hx

end InfoGeometry.Canonical.SplitAlbertPeirceQuadraticRepresentation
end noncomputable section
