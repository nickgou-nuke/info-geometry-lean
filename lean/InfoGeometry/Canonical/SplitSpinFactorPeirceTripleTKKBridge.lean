import InfoGeometry.Canonical.SplitSpinFactorTKKSO66
import InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction

/-! Compatibility path for the Peirce/TKK bridge.  The active repository
proves the Peirce-zero restriction and conformal TKK identities in separate
owners; this bridge exposes their common carrier without asserting a new
ambient exceptional identification. -/
namespace InfoGeometry.Canonical.SplitSpinFactorPeirceTripleTKKBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitSpinFactorTKKSO66

abbrev H3 := H3Zorn ℝ
abbrev V10 := SplitSpinFactorTKKSO66.V10

theorem jordanTriple_preserves_peirceZero
    {x y z : H3} (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) := by
  exact InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction.peirceZero_triple_closure
    x y z hx hy hz

end InfoGeometry.Canonical.SplitSpinFactorPeirceTripleTKKBridge
