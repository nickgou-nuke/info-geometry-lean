/-!
# Vendored GIFT octonion coordinate compatibility surface

The upstream gitlink historically used by this repository is no longer
materializable from a clean checkout.  Repository-wide search shows that the
only imported GIFT declaration is the coordinate carrier
`GIFT.Algebraic.Octonions.Octonion`, used by `Canonical.HopfTest` to define a
sum-of-squares readout.

This compatibility module intentionally preserves only that consumed surface.
It does not claim GIFT's multiplication, alternativity, norm composition, or
G₂ results.
-/

namespace GIFT.Algebraic.Octonions

/-- Eight-coordinate octonion-shaped carrier used by the local Hopf readout. -/
structure Octonion (R : Type*) where
  re : R
  e1 : R
  e2 : R
  e3 : R
  e4 : R
  e5 : R
  e6 : R
  e7 : R
  deriving Repr

end GIFT.Algebraic.Octonions
