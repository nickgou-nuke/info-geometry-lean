import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentAtlasTopCat
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of an atlas-local relative feature region

The atlas already records a finite open cover and chart compatibilities.  This
owner packages a single atlas-local relative feature region as a subtype and
records its evaluation into the ambient feature space, together with the
factorization through the region subtype.
-/

def symbolicLatentFeatureSpaceInclusionTopCatHom
    {ι : Type} [Fintype ι]
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of R ⟶ TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def SymbolicLatentAtlas.relativeFeatureRegionObservationTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of (A.relativeFeatureRegion k R) ⟶ TopCat.of R :=
  TopCat.ofHom
    { toFun := fun x =>
        ⟨symbolicObservationMap (A.chart k).system x.1, x.2.2⟩
      continuous_toFun := by
        exact ((continuous_symbolicObservationMap (A.chart k).system).comp
          continuous_subtype_val).subtype_mk (fun x => x.2.2) }

theorem SymbolicLatentAtlas.relativeFeatureRegionObservationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    (x : A.relativeFeatureRegion k R) :
    A.relativeFeatureRegionObservationTopCatHom k R x =
      ⟨symbolicObservationMap (A.chart k).system x.1, x.2.2⟩ :=
  rfl

def SymbolicLatentAtlas.relativeFeatureRegionObservationAmbientTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of (A.relativeFeatureRegion k R) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := fun x => symbolicObservationMap (A.chart k).system x.1
      continuous_toFun :=
        (continuous_symbolicObservationMap (A.chart k).system).comp
          continuous_subtype_val }

theorem SymbolicLatentAtlas.relativeFeatureRegionObservationAmbientTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    (x : A.relativeFeatureRegion k R) :
    A.relativeFeatureRegionObservationAmbientTopCatHom k R x =
      symbolicObservationMap (A.chart k).system x.1 :=
  rfl

theorem SymbolicLatentAtlas.relativeFeatureRegionObservation_factorization
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι)) :
    A.relativeFeatureRegionObservationTopCatHom k R ≫
        symbolicLatentFeatureSpaceInclusionTopCatHom R =
      A.relativeFeatureRegionObservationAmbientTopCatHom k R := by
  ext x
  rfl

theorem SymbolicLatentAtlas.relativeFeatureRegionObservation_unique
    {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : SymbolicLatentAtlas X ι κ)
    (k : κ) (R : Set (SymbolicFeatureSpace ι))
    {u : TopCat.of (A.relativeFeatureRegion k R) ⟶ TopCat.of R}
    (hu : u ≫ symbolicLatentFeatureSpaceInclusionTopCatHom R =
      A.relativeFeatureRegionObservationAmbientTopCatHom k R) :
    u = A.relativeFeatureRegionObservationTopCatHom k R := by
  apply TopCat.hom_ext
  ext x i
  have hx := congrArg (fun m => m x i) hu
  simpa [SymbolicLatentAtlas.relativeFeatureRegionObservationTopCatHom,
    symbolicLatentFeatureSpaceInclusionTopCatHom,
    SymbolicLatentAtlas.relativeFeatureRegionObservationAmbientTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hx

end InfoGeometry.Topology
