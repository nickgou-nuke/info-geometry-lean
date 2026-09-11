import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartMorphism

namespace InfoGeometry.Topology

open CategoryTheory

/-!
Native `TopCat` packaging for symbolic-latent chart morphisms.

The underlying chart owner already proves continuity and the feature
intertwining equation.  This file exposes those facts as categorical
morphisms and as a commuting square; it does not add metric or analytic
structure to the latent carriers.
-/

def SymbolicLatentChart.observationTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (C : SymbolicLatentChart X ι) :
    TopCat.of X ⟶ TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := symbolicObservationMap C.system
      continuous_toFun := continuous_symbolicObservationMap C.system }

def SymbolicLatentChartMorphism.toFunTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) :
    TopCat.of X ⟶ TopCat.of Y :=
  TopCat.ofHom
    { toFun := F.toFun
      continuous_toFun := F.continuous_toFun }

def SymbolicLatentChartMorphism.featureMapTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) :
    TopCat.of (SymbolicFeatureSpace ι) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom
    { toFun := F.featureMap
      continuous_toFun := F.continuous_featureMap }

theorem SymbolicLatentChartMorphism.toFunTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) (x : X) :
    F.toFunTopCatHom x = F.toFun x := rfl

theorem SymbolicLatentChartMorphism.featureMapTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (z : SymbolicFeatureSpace ι) :
    F.featureMapTopCatHom z = F.featureMap z := rfl

theorem SymbolicLatentChartMorphism.feature_intertwining_topCat
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) :
    F.toFunTopCatHom ≫ D.observationTopCatHom =
      C.observationTopCatHom ≫ F.featureMapTopCatHom := by
  apply TopCat.hom_ext
  ext x i
  exact congrFun (F.intertwines x).symm i

def SymbolicLatentChart.latentFeatureRegionInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (C : SymbolicLatentChart X ι)
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of {x // x ∈ latentFeatureRegion C R} ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def SymbolicLatentChartMorphism.latentFeatureRegionTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    TopCat.of {x // x ∈ latentFeatureRegion C (F.featureMap ⁻¹' R)} ⟶
      TopCat.of {y // y ∈ latentFeatureRegion D R} :=
  TopCat.ofHom
    { toFun := F.latentFeatureRegionMap R
      continuous_toFun := F.continuous_latentFeatureRegionMap R }

theorem SymbolicLatentChartMorphism.latentFeatureRegionTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (x : {x // x ∈ latentFeatureRegion C (F.featureMap ⁻¹' R)}) :
    F.latentFeatureRegionTopCatHom R x = F.latentFeatureRegionMap R x := rfl

theorem SymbolicLatentChartMorphism.latentFeatureRegion_factorization_topCat
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    F.latentFeatureRegionTopCatHom R ≫
        D.latentFeatureRegionInclusionTopCatHom R =
      C.latentFeatureRegionInclusionTopCatHom (F.featureMap ⁻¹' R) ≫
        F.toFunTopCatHom := by
  apply TopCat.hom_ext
  ext x
  rfl

end InfoGeometry.Topology
