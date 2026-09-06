import InfoGeometry.Canonical.SplitG2GaugeCochainCurvature
import InfoGeometry.Canonical.SplitG2GaugeHodgeCurvatureBridge

namespace InfoGeometry.Canonical

/-!
# Gauge-covariant split-`G₂` cochains

This is a compatibility bridge over the already verified discrete gauge
owners.  It reexports the curvature data, the flatness readout, and the
Hodge-compatible face holonomy statements under a shorter `G₂`-prefixed
namespace.

It does not introduce a new connection theory or a stronger covariance law
than the existing discrete owner files.
-/

/-- Compatibility alias for the discrete split-`G₂` covariant cochain data. -/
abbrev G2GaugeCovariantCochainData := SplitG2CovariantCochainData

/-- Compatibility alias for the discrete split-`G₂` Hodge-covariant data. -/
abbrev G2GaugeHodgeCovariantCochainData := SplitG2HodgeCovariantCochainData

namespace G2GaugeCovariantCochainData

theorem covariantCoboundary_sq_eq_curvature
    {K : FiniteOrientedCellComplex}
    (D : G2GaugeCovariantCochainData K) :
    D.covariantCoboundary1.comp D.covariantCoboundary0 = D.curvatureAction :=
  SplitG2CovariantCochainData.covariantCoboundary_sq_eq_curvature D

theorem covariantCoboundary_sq_zero_of_flat
    {K : FiniteOrientedCellComplex}
    (D : G2GaugeCovariantCochainData K)
    (hflat : D.Flat) :
    D.covariantCoboundary1.comp D.covariantCoboundary0 = 0 :=
  SplitG2CovariantCochainData.covariantCoboundary_sq_zero_of_flat D hflat

theorem faceHolonomy_preserves_threeForm
    {K : FiniteOrientedCellComplex}
    (D : G2GaugeCovariantCochainData K)
    (σ : K.Cell 2)
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (D.faceHolonomy σ x)
        (D.faceHolonomy σ y)
        (D.faceHolonomy σ z) =
      canonicalSplitG2ThreeFormValue x y z :=
  SplitG2CovariantCochainData.faceHolonomy_preserves_threeForm D σ x y z

end G2GaugeCovariantCochainData

namespace G2GaugeHodgeCovariantCochainData

theorem faceHolonomy_preserves_coassociativeFourForm
    {K : FiniteOrientedCellComplex}
    (D : G2GaugeHodgeCovariantCochainData K)
    (σ : K.Cell 2)
    (φ : SplitG2ThreeForms)
    (hφ : pullbackForm 3 (D.base.faceHolonomy σ).toLinearEquiv φ = φ) :
    pullbackForm 4 (D.base.faceHolonomy σ).toLinearEquiv
        (D.hodgeData.star34 φ) =
      D.hodgeData.star34 φ :=
  SplitG2HodgeCovariantCochainData.faceHolonomy_preserves_coassociativeFourForm D σ φ hφ

theorem faceTransportFourCochain_eq_of_invariant
    {K : FiniteOrientedCellComplex}
    (D : G2GaugeHodgeCovariantCochainData K)
    (F : SplitG2DiscreteCoframe K)
    (σ : K.Cell 2)
    (φ : SplitG2ThreeForms)
    (hφ : pullbackForm 3 (D.base.faceHolonomy σ).toLinearEquiv φ = φ) :
    SplitG2HodgeCovariantCochainData.faceTransportFourCochain D F σ φ =
      pullbackFourForm F (D.hodgeData.star34 φ) :=
  SplitG2HodgeCovariantCochainData.faceTransportFourCochain_eq_of_invariant D F σ φ hφ

end G2GaugeHodgeCovariantCochainData

end InfoGeometry.Canonical
