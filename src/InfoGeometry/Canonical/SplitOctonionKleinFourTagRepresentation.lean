import InfoGeometry.Canonical.KleinFourTagRootNormalization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionKleinFourAutomorphism

/-!
# Multiplicative presentation of the native split-octonion axis action

`KleinFourTag.Tag` is additive.  This owner exposes the already-proved
split-octonion axis action through `Multiplicative Tag`, so it can be used as
a genuine monoid representation without introducing another four-element
source or reproving the automorphism laws.
-/

namespace InfoGeometry.Canonical.SplitOctonionKleinFourTagRepresentation

open InfoGeometry.Canonical.KleinFourTagRootNormalization
open InfoGeometry.Canonical.SplitOctonionKleinFourAutomorphism
open InfoGeometry.Geometry.KleinFourTag

abbrev AxisCarrier := SplitOct
abbrev V4 := InfoGeometry.Canonical.KleinFourTagRootNormalization.V4
local instance : Mul AxisCarrier :=
  InfoGeometry.Canonical.SplitOctonionKleinFourAutomorphism.instMulSplitOct

def axisActionHom : V4 →* (AxisCarrier ≃* AxisCarrier) where
  toFun g := axisAction (g : V4Add)
  map_one' := by
    rfl
  map_mul' := by
    intro g h
    apply MulEquiv.ext
    intro X
    change axisAction (Multiplicative.toAdd g + Multiplicative.toAdd h) X =
      axisAction (Multiplicative.toAdd g)
        (axisAction (Multiplicative.toAdd h) X)
    exact axisAction_mul_apply (Multiplicative.toAdd g)
      (Multiplicative.toAdd h) X

theorem axisActionHom_apply (g : V4) (X : AxisCarrier) :
    axisActionHom g X = axisAction (g : V4Add) X := rfl

end InfoGeometry.Canonical.SplitOctonionKleinFourTagRepresentation
