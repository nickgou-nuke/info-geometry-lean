import InfoGeometry.Canonical.RealStageProjectionDyadicCocone
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Additive readout on the concrete dyadic direct limit

The additive structure is inherited from the existing equivalence with
`DyadicRational`; no compatible-family wrapper is needed.
-/

theorem dyadicDirectLimitEquiv_add
    (x y : DyadicDirectLimit) :
    dyadicDirectLimitEquiv (x + y) =
      dyadicDirectLimitEquiv x + dyadicDirectLimitEquiv y := by
  exact dyadicDirectLimitAddEquiv.map_add x y

theorem dyadicDirectLimitEquiv_neg
    (x : DyadicDirectLimit) :
    dyadicDirectLimitEquiv (-x) = -dyadicDirectLimitEquiv x := by
  exact dyadicDirectLimitAddEquiv.map_neg x

end InfoGeometry.Canonical
