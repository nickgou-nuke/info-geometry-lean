import InfoGeometry.Topology.SymbolicLatentAtlasClosedRegionTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of an atlas-local closed feature region

The atlas owner already proves that a relative feature region inside a chart
domain is closed.  This file transports that existing subtype into `CompHaus`
when the chart domain is compact Hausdorff and the target feature region is
itself compact.  The observation map is lifted without introducing a second
carrier or asserting compactness of the ambient feature space.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι κ : Type} [TopologicalSpace X]
  [Fintype ι] [Fintype κ]

noncomputable def symbolicLatentAtlasRelativeFeatureRegionInDomainCompHaus
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) : CompHaus := by
  letI : CompactSpace (A.relativeFeatureRegionInDomain k R) :=
    isCompact_iff_compactSpace.mp
      (A.relativeFeatureRegionInDomain_isCompact k R hR)
  exact CompHaus.of (A.relativeFeatureRegionInDomain k R)

noncomputable def symbolicLatentAtlasFeatureRegionCompHaus
    (R : Set (SymbolicFeatureSpace ι))
    (hRcompact : IsCompact R) : CompHaus := by
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hRcompact
  exact CompHaus.of R

noncomputable def symbolicLatentAtlasRelativeFeatureRegionObservationCompHausHom
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) (hRcompact : IsCompact R) :
    symbolicLatentAtlasRelativeFeatureRegionInDomainCompHaus A k R hR ⟶
      symbolicLatentAtlasFeatureRegionCompHaus R hRcompact := by
  letI : CompactSpace (A.relativeFeatureRegionInDomain k R) :=
    isCompact_iff_compactSpace.mp
      (A.relativeFeatureRegionInDomain_isCompact k R hR)
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hRcompact
  change CompHaus.of (A.relativeFeatureRegionInDomain k R) ⟶ CompHaus.of R
  exact ⟨A.relativeFeatureRegionInDomainObservationTopCatHom k R⟩

theorem symbolicLatentAtlasRelativeFeatureRegionObservationCompHausHom_forget
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) (hRcompact : IsCompact R) :
    compHausToTop.map
        (symbolicLatentAtlasRelativeFeatureRegionObservationCompHausHom
          A k R hR hRcompact) =
      A.relativeFeatureRegionInDomainObservationTopCatHom k R := by
  rfl

end InfoGeometry.Topology

end
