import InfoGeometry.Topology.SymbolicLatentAtlasClosedRegionCompHaus

/-!
# `TopCat` readout of a compact closed atlas-local feature region

The `CompHaus` owner supplies the compact carrier and its restricted
observation map.  This file records the corresponding maps after forgetting
to `TopCat`; no compactness of the ambient feature space is assumed.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X ι κ : Type} [TopologicalSpace X]
  [Fintype ι] [Fintype κ]

def SymbolicLatentAtlas.relativeFeatureRegionInDomainCompHausInclusionTopCatHom
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) :
    compHausToTop.obj
        (symbolicLatentAtlasRelativeFeatureRegionInDomainCompHaus A k R hR) ⟶
      TopCat.of (SymbolicLatentAtlasDomain A k) := by
  change TopCat.of (A.relativeFeatureRegionInDomain k R) ⟶
    TopCat.of (SymbolicLatentAtlasDomain A k)
  exact A.relativeFeatureRegionInDomainInclusionTopCatHom k R

def SymbolicLatentAtlas.relativeFeatureRegionInDomainCompHausObservationTopCatHom
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) :
    compHausToTop.obj
        (symbolicLatentAtlasRelativeFeatureRegionInDomainCompHaus A k R hR) ⟶
      TopCat.of R := by
  change TopCat.of (A.relativeFeatureRegionInDomain k R) ⟶ TopCat.of R
  exact A.relativeFeatureRegionInDomainObservationTopCatHom k R

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomainCompHausInclusionTopCatHom_forget
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) :
    A.relativeFeatureRegionInDomainCompHausInclusionTopCatHom k R hR =
      A.relativeFeatureRegionInDomainInclusionTopCatHom k R := by
  rfl

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomainCompHausObservationTopCatHom_forget
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) :
    A.relativeFeatureRegionInDomainCompHausObservationTopCatHom k R hR =
      A.relativeFeatureRegionInDomainObservationTopCatHom k R := by
  rfl

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomainCompHausObservation_factorization
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    [T2Space (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) :
    A.relativeFeatureRegionInDomainCompHausObservationTopCatHom
        k R hR ≫
        symbolicLatentFeatureSpaceInclusionTopCatHom R =
      A.relativeFeatureRegionInDomainObservationAmbientTopCatHom k R := by
  exact A.relativeFeatureRegionInDomainObservation_factorization k R

end InfoGeometry.Topology
