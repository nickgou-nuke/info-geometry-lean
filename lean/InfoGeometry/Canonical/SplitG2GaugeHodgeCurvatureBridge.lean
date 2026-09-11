import InfoGeometry.Canonical.SplitG2GaugeCochainCurvature
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitG2HodgeTransportBridge

namespace InfoGeometry.Canonical

/-!
# Curvature transport of the Hodge pair

The face holonomy already preserves the canonical three-form.  Preservation of
the Hodge-dual four-form additionally requires compatibility with the chosen
`star34`; this file packages that extra datum and derives the corresponding
four-form statements.
-/

structure SplitG2HodgeCovariantCochainData
    (K : FiniteOrientedCellComplex)
    where
  base : SplitG2CovariantCochainData K
  hodgeData : SplitG2HodgeDualData
  hodgeCompatible :
    ∀ (σ : K.Cell 2) (φ : SplitG2ThreeForms),
      pullbackForm 4 (base.faceHolonomy σ).toLinearEquiv
          (hodgeData.star34 φ) =
        hodgeData.star34
          (pullbackForm 3 (base.faceHolonomy σ).toLinearEquiv φ)

namespace SplitG2HodgeCovariantCochainData

def faceHodgeAutomorphism
    {K : FiniteOrientedCellComplex}
    (D : SplitG2HodgeCovariantCochainData K)
    (σ : K.Cell 2) :
    SplitG2HodgeCompatibleAutomorphism D.hodgeData where
  automorphism := D.base.faceHolonomy σ
  star34_compatible := D.hodgeCompatible σ

theorem faceHolonomy_preserves_coassociativeFourForm
    {K : FiniteOrientedCellComplex}
    (D : SplitG2HodgeCovariantCochainData K)
    (σ : K.Cell 2)
    (φ : SplitG2ThreeForms)
    (hφ : pullbackForm 3 (D.base.faceHolonomy σ).toLinearEquiv φ = φ) :
    pullbackForm 4 (D.base.faceHolonomy σ).toLinearEquiv
        (D.hodgeData.star34 φ) =
      D.hodgeData.star34 φ := by
  exact (D.faceHodgeAutomorphism σ).preserves_coassociativeFourForm φ hφ

noncomputable def faceTransportFourCochain
    {K : FiniteOrientedCellComplex}
    (D : SplitG2HodgeCovariantCochainData K)
    (F : SplitG2DiscreteCoframe K)
    (σ : K.Cell 2)
    (φ : SplitG2ThreeForms) :
    RationalScalarCochain K 4 :=
  pathTransportFourCochain D.base.connection F (D.base.faceBoundary σ)
    (D.hodgeData.star34 φ)

theorem faceTransportFourCochain_eq_of_invariant
    {K : FiniteOrientedCellComplex}
    (D : SplitG2HodgeCovariantCochainData K)
    (F : SplitG2DiscreteCoframe K)
    (σ : K.Cell 2)
    (φ : SplitG2ThreeForms)
    (hφ : pullbackForm 3 (D.base.faceHolonomy σ).toLinearEquiv φ = φ) :
    faceTransportFourCochain D F σ φ =
      pullbackFourForm F (D.hodgeData.star34 φ) := by
  apply pathTransportFourCochain_eq_of_invariant
  exact D.faceHolonomy_preserves_coassociativeFourForm σ φ hφ

end SplitG2HodgeCovariantCochainData

end InfoGeometry.Canonical
