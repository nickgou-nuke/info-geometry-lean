import InfoGeometry.Canonical.SplitG2DiscreteGaugeCochain

namespace InfoGeometry.Canonical

/-!
# Covariant cellular cochains and curvature

The cell complex does not by itself provide endpoint maps or a connection
action.  This owner therefore packages those choices explicitly.  The
curvature equation is a structure field, while flatness is a separate
property.  This prevents a differential-geometric conclusion from being
silently inferred from the pointwise split-octonion algebra.
-/

abbrev SplitG2GaugeCochain
    (K : FiniteOrientedCellComplex) (p : ℕ) :=
  K.Cell p → imaginarySplitOctonion

structure SplitG2CovariantCochainData
    (K : FiniteOrientedCellComplex) where
  connection : SplitG2GaugeConnection (K.Cell 1)
  faceBoundary : K.Cell 2 → List (K.Cell 1)
  covariantCoboundary0 :
    SplitG2GaugeCochain K 0 →ₗ[ℚ] SplitG2GaugeCochain K 1
  covariantCoboundary1 :
    SplitG2GaugeCochain K 1 →ₗ[ℚ] SplitG2GaugeCochain K 2
  curvatureAction :
    SplitG2GaugeCochain K 0 →ₗ[ℚ] SplitG2GaugeCochain K 2
  square_eq_curvature :
    covariantCoboundary1.comp covariantCoboundary0 = curvatureAction

namespace SplitG2CovariantCochainData

def faceHolonomy
    {K : FiniteOrientedCellComplex}
    (D : SplitG2CovariantCochainData K)
    (σ : K.Cell 2) : SplitG2Automorphism :=
  parallelTransport D.connection (D.faceBoundary σ)

theorem covariantCoboundary_sq_eq_curvature
    {K : FiniteOrientedCellComplex}
    (D : SplitG2CovariantCochainData K) :
    D.covariantCoboundary1.comp D.covariantCoboundary0 =
      D.curvatureAction :=
  D.square_eq_curvature

def Flat
    {K : FiniteOrientedCellComplex}
    (D : SplitG2CovariantCochainData K) : Prop :=
  D.curvatureAction = 0

theorem covariantCoboundary_sq_zero_of_flat
    {K : FiniteOrientedCellComplex}
    (D : SplitG2CovariantCochainData K)
    (hflat : D.Flat) :
    D.covariantCoboundary1.comp D.covariantCoboundary0 = 0 := by
  rw [D.covariantCoboundary_sq_eq_curvature, hflat]

theorem faceHolonomy_preserves_threeForm
    {K : FiniteOrientedCellComplex}
    (D : SplitG2CovariantCochainData K)
    (σ : K.Cell 2)
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (D.faceHolonomy σ x)
        (D.faceHolonomy σ y)
        (D.faceHolonomy σ z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact parallelTransport_preserves_threeForm
    D.connection (D.faceBoundary σ) x y z

theorem faceHolonomy_preserves_threeForm_on_flat_data
    {K : FiniteOrientedCellComplex}
    (D : SplitG2CovariantCochainData K)
    (σ : K.Cell 2)
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (D.faceHolonomy σ x)
        (D.faceHolonomy σ y)
        (D.faceHolonomy σ z) =
      canonicalSplitG2ThreeFormValue x y z :=
  D.faceHolonomy_preserves_threeForm σ x y z

end SplitG2CovariantCochainData

end InfoGeometry.Canonical
