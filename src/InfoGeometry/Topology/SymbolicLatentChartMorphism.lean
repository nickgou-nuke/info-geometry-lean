import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentSpace

/-!
# Morphisms of symbolic latent charts

This owner separates the latent map from the induced map on feature vectors.
The intertwining equation is the only semantic requirement: no metric,
probability, or physical interpretation is assumed.
-/

namespace InfoGeometry.Topology

abbrev SymbolicFeatureSpace (ι : Type*) := ι → ℝ

def latentFeatureRegion
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι)
    (R : Set (SymbolicFeatureSpace ι)) : Set X :=
  symbolicObservationMap C.system ⁻¹' R

theorem isClosed_latentFeatureRegion
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι)
    (R : Set (SymbolicFeatureSpace ι))
    (hR : IsClosed R) :
    IsClosed (latentFeatureRegion C R) := by
  exact hR.preimage (continuous_symbolicObservationMap C.system)

theorem isClosedEmbedding_latentFeatureRegion_subtypeVal
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι)
    (R : Set (SymbolicFeatureSpace ι))
    (hR : IsClosed R) :
    Topology.IsClosedEmbedding
      (Subtype.val : {x // x ∈ latentFeatureRegion C R} → X) := by
  exact (isClosed_latentFeatureRegion C R hR).isClosedEmbedding_subtypeVal

structure SymbolicLatentChartMorphism
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι)
    (D : SymbolicLatentChart Y ι) where
  toFun : X → Y
  continuous_toFun : Continuous toFun
  featureMap : SymbolicFeatureSpace ι → SymbolicFeatureSpace ι
  continuous_featureMap : Continuous featureMap
  intertwines : ∀ x,
    featureMap (symbolicObservationMap C.system x) =
      symbolicObservationMap D.system (toFun x)

namespace SymbolicLatentChartMorphism

open CategoryTheory

def id
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι) :
    SymbolicLatentChartMorphism C C where
  toFun := fun x => x
  continuous_toFun := continuous_id
  featureMap := fun x => x
  continuous_featureMap := continuous_id
  intertwines := by intro x; rfl

def comp
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D) :
    SymbolicLatentChartMorphism C E where
  toFun := G.toFun ∘ F.toFun
  continuous_toFun := G.continuous_toFun.comp F.continuous_toFun
  featureMap := G.featureMap ∘ F.featureMap
  continuous_featureMap := G.continuous_featureMap.comp F.continuous_featureMap
  intertwines := by
    intro x
    change G.featureMap
        (F.featureMap (symbolicObservationMap C.system x)) =
      symbolicObservationMap E.system (G.toFun (F.toFun x))
    rw [F.intertwines, G.intertwines]

theorem map_latentFeatureRegion
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    F.toFun '' latentFeatureRegion C (F.featureMap ⁻¹' R) ⊆
      latentFeatureRegion D R := by
  rintro y ⟨x, hx, rfl⟩
  change symbolicObservationMap D.system (F.toFun x) ∈ R
  rw [← F.intertwines x]
  exact hx

theorem continuous_toFun_on_latentFeatureRegion
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    ContinuousOn F.toFun (latentFeatureRegion C (F.featureMap ⁻¹' R)) :=
  F.continuous_toFun.continuousOn

def latentFeatureRegionMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    {x // x ∈ latentFeatureRegion C (F.featureMap ⁻¹' R)} →
      {y // y ∈ latentFeatureRegion D R} :=
  fun x => ⟨F.toFun x, F.map_latentFeatureRegion R
    ⟨x, x.property, rfl⟩⟩

theorem continuous_latentFeatureRegionMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    Continuous (F.latentFeatureRegionMap R) := by
  exact (F.continuous_toFun.comp continuous_subtype_val).subtype_mk
    (fun x => F.map_latentFeatureRegion R ⟨x, x.property, rfl⟩)

@[simp] theorem comp_toFun
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D) :
    (G.comp F).toFun = G.toFun ∘ F.toFun :=
  rfl

@[simp] theorem comp_featureMap
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D) :
    (G.comp F).featureMap = G.featureMap ∘ F.featureMap :=
  rfl

end SymbolicLatentChartMorphism

end InfoGeometry.Topology
