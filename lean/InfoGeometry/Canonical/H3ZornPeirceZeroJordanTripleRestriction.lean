import InfoGeometry.Canonical.SplitAlbertPeirceZeroJordanTripleRestriction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Compatibility path for the upstream H3 Peirce-zero triple restriction.
The theorem is delegated to the current Split-Albert owner. -/
namespace InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

abbrev H3 := H3Zorn ℝ

theorem candidateJordanTriple_preserves_peirceZero
    {x y z : H3} (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) :=
  SplitAlbertPeirceZeroJordanTripleRestriction.candidateJordanTriple_preserves_peirceZero
    hx hy hz

theorem peirceZero_triple_closure
    (x y z : H3) (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) :=
  candidateJordanTriple_preserves_peirceZero hx hy hz

end InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction
