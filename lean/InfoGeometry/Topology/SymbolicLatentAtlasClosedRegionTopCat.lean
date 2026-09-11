import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentAtlasTopCat
import InfoGeometry.Topology.SymbolicLatentAtlasFeatureRegionTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` maps for closed atlas-local feature regions

`relativeFeatureRegionInDomain` is a closed subset of a chart domain when the
feature target is closed.  This owner exposes that subtype as a genuine
`TopCat` object and records its observation factorization through the domain
and feature subtypes.
-/

def SymbolicLatentAtlas.relativeFeatureRegionInDomainInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of (A.relativeFeatureRegionInDomain k R) ⟶
      TopCat.of (SymbolicLatentAtlasDomain A k) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def SymbolicLatentAtlas.relativeFeatureRegionInDomainObservationTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of (A.relativeFeatureRegionInDomain k R) ⟶ TopCat.of R :=
  TopCat.ofHom
    { toFun := fun x =>
        ⟨symbolicObservationMap (A.chart k).system x.1.1, x.2⟩
      continuous_toFun := by
        exact ((continuous_symbolicObservationMap (A.chart k).system).comp
          continuous_subtype_val).comp continuous_subtype_val |>.subtype_mk
          (fun x => x.2) }

def SymbolicLatentAtlas.relativeFeatureRegionInDomainObservationAmbientTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of (A.relativeFeatureRegionInDomain k R) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := fun x => symbolicObservationMap (A.chart k).system x.1.1
      continuous_toFun :=
        ((continuous_symbolicObservationMap (A.chart k).system).comp
          continuous_subtype_val).comp continuous_subtype_val }

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomainObservationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    (x : A.relativeFeatureRegionInDomain k R) :
    A.relativeFeatureRegionInDomainObservationTopCatHom k R x =
      ⟨symbolicObservationMap (A.chart k).system x.1.1, x.2⟩ :=
  rfl

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomainObservationAmbientTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    (x : A.relativeFeatureRegionInDomain k R) :
    A.relativeFeatureRegionInDomainObservationAmbientTopCatHom k R x =
      symbolicObservationMap (A.chart k).system x.1.1 :=
  rfl

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomainObservation_factorization
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    A.relativeFeatureRegionInDomainObservationTopCatHom k R ≫
        symbolicLatentFeatureSpaceInclusionTopCatHom R =
      A.relativeFeatureRegionInDomainObservationAmbientTopCatHom k R := by
  ext x
  rfl

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomainObservation_unique
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    {u : TopCat.of (A.relativeFeatureRegionInDomain k R) ⟶ TopCat.of R}
    (hu : u ≫ symbolicLatentFeatureSpaceInclusionTopCatHom R =
      A.relativeFeatureRegionInDomainObservationAmbientTopCatHom k R) :
    u = A.relativeFeatureRegionInDomainObservationTopCatHom k R := by
  apply TopCat.hom_ext
  ext x i
  have hx := congrArg (fun m => m x i) hu
  simpa [SymbolicLatentAtlas.relativeFeatureRegionInDomainObservationTopCatHom,
    symbolicLatentFeatureSpaceInclusionTopCatHom,
    SymbolicLatentAtlas.relativeFeatureRegionInDomainObservationAmbientTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hx

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomain_isClosed_subtype
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) (hR : IsClosed R) :
    IsClosed (A.relativeFeatureRegionInDomain k R) :=
  A.isClosed_relativeFeatureRegionInDomain k R hR

theorem SymbolicLatentAtlas.relativeFeatureRegionInDomain_isCompact
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    [CompactSpace (SymbolicLatentAtlasDomain A k)]
    (hR : IsClosed R) :
    IsCompact (A.relativeFeatureRegionInDomain k R) :=
  (A.isClosed_relativeFeatureRegionInDomain k R hR).isCompact

end InfoGeometry.Topology
