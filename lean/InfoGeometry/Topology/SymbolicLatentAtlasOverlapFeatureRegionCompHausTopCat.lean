import InfoGeometry.Topology.SymbolicLatentAtlasOverlapFeatureRegionCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Feature-region observation squares in `CompHaus`

The compact feature-region transport is already available as a `CompHaus`
isomorphism.  This owner exposes the corresponding restricted observation
maps and proves their transition square.  The target feature space remains
in `TopCat`, since no compactness of the ambient feature space is assumed.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

def SymbolicLatentAtlas.overlapFeatureRegionSourceObservationCompHausTopCatHom
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) :
    compHausToTop.obj (A.overlapFeatureRegionSourceCompHaus H R hcompact) ⟶
      TopCat.of (SymbolicFeatureSpace ι) := by
  change TopCat.of {x // x ∈ A.overlapFeatureRegionSource H R} ⟶
    TopCat.of (SymbolicFeatureSpace ι)
  exact TopCat.ofHom
    { toFun := fun x => symbolicObservationMap (A.chart i).system x.1
      continuous_toFun :=
        (continuous_symbolicObservationMap (A.chart i).system).comp
          continuous_subtype_val }

def SymbolicLatentAtlas.overlapFeatureRegionTargetObservationCompHausTopCatHom
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) :
    compHausToTop.obj (A.overlapFeatureRegionTargetCompHaus H R hcompact) ⟶
      TopCat.of (SymbolicFeatureSpace ι) := by
  change TopCat.of {x // x ∈ A.overlapFeatureRegionTarget H R} ⟶
    TopCat.of (SymbolicFeatureSpace ι)
  exact TopCat.ofHom
    { toFun := fun x => symbolicObservationMap (A.chart j).system x.1
      continuous_toFun :=
        (continuous_symbolicObservationMap (A.chart j).system).comp
          continuous_subtype_val }

@[simp] theorem SymbolicLatentAtlas.overlapFeatureRegionSourceObservationCompHausTopCatHom_apply
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R))
    (x : {x // x ∈ A.overlapFeatureRegionSource H R}) :
    A.overlapFeatureRegionSourceObservationCompHausTopCatHom H R hcompact x =
      symbolicObservationMap (A.chart i).system x.1 :=
  rfl

@[simp] theorem SymbolicLatentAtlas.overlapFeatureRegionTargetObservationCompHausTopCatHom_apply
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R))
    (x : {x // x ∈ A.overlapFeatureRegionTarget H R}) :
    A.overlapFeatureRegionTargetObservationCompHausTopCatHom H R hcompact x =
      symbolicObservationMap (A.chart j).system x.1 :=
  rfl

theorem SymbolicLatentAtlas.overlapFeatureRegionObservation_transition_commutes
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) :
    A.overlapFeatureRegionSourceObservationCompHausTopCatHom H R hcompact ≫
        H.featureTransitionTopCatHom =
      (compHausToTop.map (A.overlapFeatureRegionCompHausIso H R hcompact).hom) ≫
        A.overlapFeatureRegionTargetObservationCompHausTopCatHom H R hcompact := by
  apply TopCat.hom_ext
  ext x l
  change H.featureEquiv
      (symbolicObservationMap (A.chart i).system x.1) l =
    (symbolicObservationMap (A.chart j).system x.1) l
  exact congrFun (H.intertwines_on_overlap x.1 x.property.1) l

theorem SymbolicLatentAtlas.overlapFeatureRegionCompHausIso_hom_forget_natural
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) :
    A.overlapFeatureRegionSourceObservationCompHausTopCatHom H R hcompact ≫
        H.featureTransitionTopCatHom =
      (compHausToTop.map (A.overlapFeatureRegionCompHausIso H R hcompact).hom) ≫
        A.overlapFeatureRegionTargetObservationCompHausTopCatHom H R hcompact :=
  A.overlapFeatureRegionObservation_transition_commutes H R hcompact

theorem SymbolicLatentAtlas.overlapFeatureRegionObservation_transition_symm_commutes
    {X ι κ : Type} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    [T2Space X]
    (A : SymbolicLatentAtlas X ι κ)
    {i j : κ} (H : SymbolicLatentAtlasCompatibility A i j)
    (R : Set (SymbolicFeatureSpace ι))
    (hcompact : IsCompact (A.overlapFeatureRegionSource H R)) :
    A.overlapFeatureRegionTargetObservationCompHausTopCatHom H R hcompact ≫
        H.symm.featureTransitionTopCatHom =
      (compHausToTop.map (A.overlapFeatureRegionCompHausIso H R hcompact).inv) ≫
        A.overlapFeatureRegionSourceObservationCompHausTopCatHom H R hcompact := by
  apply TopCat.hom_ext
  ext x l
  change H.symm.featureEquiv
      (symbolicObservationMap (A.chart j).system x.1) l =
    (symbolicObservationMap (A.chart i).system x.1) l
  have hxji : x.1 ∈ A.overlap j i :=
    ⟨x.property.1.2, x.property.1.1⟩
  exact congrFun (H.symm.intertwines_on_overlap x.1 hxji) l

end InfoGeometry.Topology
