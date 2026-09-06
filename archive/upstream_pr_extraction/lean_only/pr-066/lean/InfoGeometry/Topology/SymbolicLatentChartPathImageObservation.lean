import Mathlib
import InfoGeometry.Topology.SymbolicLatentChartPathObservation
import InfoGeometry.Topology.SymbolicLatentChartMorphismTopCat
import InfoGeometry.Topology.SymbolicLatentPathImage
import InfoGeometry.Topology.SymbolicLatentPathImageFeasibleCompHaus
import InfoGeometry.Topology.SymbolicLatentPathImageTopCat

/-!
# Image transport for chart-observed symbolic paths

The bundled path-intertwining theorem induces an exact equality of observed
path images.  This owner keeps the statement at the set level, where it can be
combined with compactness and feasible-region subspace constructions.
-/

namespace InfoGeometry.Topology

open CategoryTheory

theorem SymbolicLatentChartMorphism.observedPathImage_eq_featureMap_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    observedSymbolicLatentPathImage D.system
        (mapSymbolicLatentPath F R γ).path =
      F.featureMap '' observedSymbolicLatentPathImage C.system γ.path := by
  change Set.range (observedPathInRegion (mapSymbolicLatentPath F R γ)) =
    F.featureMap '' Set.range (observedPathInRegion γ)
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨observedPathInRegion γ t, ⟨t, rfl⟩, ?_⟩
    exact (mapSymbolicLatentPath_observation F R γ t).symm
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    exact mapSymbolicLatentPath_observation F R γ t

theorem SymbolicLatentChartMorphism.featureMap_observedPathImage_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    F.featureMap '' observedSymbolicLatentPathImage C.system γ.path ⊆ R := by
  rintro z ⟨y, ⟨t, rfl⟩, rfl⟩
  have ht := γ.stays_in_region t
  change symbolicObservationMap C.system (γ.path t) ∈
    F.featureMap ⁻¹' R at ht
  exact ht

theorem SymbolicLatentChartMorphism.observedPathImage_mapped_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    observedSymbolicLatentPathImage D.system
        (mapSymbolicLatentPath F R γ).path ⊆ R := by
  rw [F.observedPathImage_eq_featureMap_image R γ]
  exact F.featureMap_observedPathImage_subset R γ

/-- The feature map induces a continuous map between the observed path-image
subtypes of a path and its mapped path. -/
def SymbolicLatentChartMorphism.observedPathImageMapTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    TopCat.of (observedSymbolicLatentPathImage C.system γ.path) ⟶
      TopCat.of (observedSymbolicLatentPathImage D.system
        (mapSymbolicLatentPath F R γ).path) :=
    TopCat.ofHom
    { toFun := fun y =>
        ⟨F.featureMap y.1, by
          rcases y.property with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [← ht]
          exact mapSymbolicLatentPath_observation F R γ t⟩
      continuous_toFun := by
        exact (F.continuous_featureMap.comp continuous_subtype_val).subtype_mk
          (fun y => by
            rcases y.property with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            change (symbolicObservationPath D.system
              (mapSymbolicLatentPath F R γ).path) t = F.featureMap y.1
            rw [← ht]
            exact mapSymbolicLatentPath_observation F R γ t) }

@[simp] theorem SymbolicLatentChartMorphism.observedPathImageMapTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R))
    (y : observedSymbolicLatentPathImage C.system γ.path) :
    F.observedPathImageMapTopCatHom R γ y =
      ⟨F.featureMap y.1, by
        rcases y.property with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [← ht]
        exact mapSymbolicLatentPath_observation F R γ t⟩ := rfl

theorem SymbolicLatentChartMorphism.observedPathImage_evaluation_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    (observedSymbolicLatentPathImageEvaluationTopCatHom
        C.system γ.path) ≫ F.observedPathImageMapTopCatHom R γ =
      observedSymbolicLatentPathImageEvaluationTopCatHom
        D.system (mapSymbolicLatentPath F R γ).path := by
  ext t x
  change (F.featureMap (observedPathInRegion γ t)) x =
    (observedPathInRegion (mapSymbolicLatentPath F R γ) t) x
  exact congrArg (fun z => z x)
    (mapSymbolicLatentPath_observation F R γ t).symm

theorem SymbolicLatentChartMorphism.observedPathImageMapTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C
      ((G.comp F).featureMap ⁻¹' R)) :
    F.observedPathImageMapTopCatHom (G.featureMap ⁻¹' R) γ ≫
        G.observedPathImageMapTopCatHom R
          (mapSymbolicLatentPath F (G.featureMap ⁻¹' R) γ) =
      (G.comp F).observedPathImageMapTopCatHom R γ := by
  ext x
  rfl

theorem SymbolicLatentChartMorphism.observedPathImageMapTopCatHom_factorization
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    F.observedPathImageMapTopCatHom R γ ≫
        observedSymbolicLatentPathImageInclusionTopCatHom D.system
          (mapSymbolicLatentPath F R γ).path =
      observedSymbolicLatentPathImageInclusionTopCatHom C.system γ.path ≫
        F.featureMapTopCatHom := by
  ext t x
  rfl

theorem SymbolicLatentChartMorphism.observedPathImageMapTopCatHom_factorization_unique
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R))
    {u : TopCat.of (observedSymbolicLatentPathImage C.system γ.path) ⟶
      TopCat.of (observedSymbolicLatentPathImage D.system
        (mapSymbolicLatentPath F R γ).path)}
    (hu : u ≫ observedSymbolicLatentPathImageInclusionTopCatHom D.system
          (mapSymbolicLatentPath F R γ).path =
      observedSymbolicLatentPathImageInclusionTopCatHom C.system γ.path ≫
        F.featureMapTopCatHom) :
    u = F.observedPathImageMapTopCatHom R γ := by
  apply TopCat.hom_ext
  ext x i
  have hx := congrArg (fun m => m x i) hu
  simpa [observedSymbolicLatentPathImageInclusionTopCatHom,
    observedPathImageMapTopCatHom, SymbolicLatentChartMorphism.featureMapTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hx

noncomputable def SymbolicLatentChartMorphism.observedPathImageMapCompHausHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    observedSymbolicLatentPathImageCompHaus C.system γ.path ⟶
      observedSymbolicLatentPathImageCompHaus D.system
        (mapSymbolicLatentPath F R γ).path := by
  letI : CompactSpace (observedSymbolicLatentPathImage C.system γ.path) :=
    observedSymbolicLatentPathImage_compactSpace C.system γ.path
  letI : CompactSpace
      (observedSymbolicLatentPathImage D.system
        (mapSymbolicLatentPath F R γ).path) :=
    observedSymbolicLatentPathImage_compactSpace D.system
      (mapSymbolicLatentPath F R γ).path
  dsimp [observedSymbolicLatentPathImageCompHaus]
  change CompHaus.of (observedSymbolicLatentPathImage C.system γ.path) ⟶
    CompHaus.of (observedSymbolicLatentPathImage D.system
      (mapSymbolicLatentPath F R γ).path)
  exact ⟨F.observedPathImageMapTopCatHom R γ⟩

theorem SymbolicLatentChartMorphism.observedPathImageMapCompHausHom_forget
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    compHausToTop.map (F.observedPathImageMapCompHausHom R γ) =
      F.observedPathImageMapTopCatHom R γ := by
  apply TopCat.hom_ext
  ext x
  rfl

theorem SymbolicLatentChartMorphism.observedPathImageMapCompHausHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C
      ((G.comp F).featureMap ⁻¹' R)) :
    F.observedPathImageMapCompHausHom (G.featureMap ⁻¹' R) γ ≫
        G.observedPathImageMapCompHausHom R
          (mapSymbolicLatentPath F (G.featureMap ⁻¹' R) γ) =
      (G.comp F).observedPathImageMapCompHausHom R γ := by
  ext x
  rfl

theorem SymbolicLatentChartMorphism.observedPathImageMapTopCatHom_start
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    F.observedPathImageMapTopCatHom R γ
        ⟨observedSymbolicLatentPath.start C.system γ.path,
          observed_start_mem_symbolicLatentPathImage C.system γ.path⟩ =
      ⟨observedSymbolicLatentPath.start D.system
          (mapSymbolicLatentPath F R γ).path,
        observed_start_mem_symbolicLatentPathImage D.system
          (mapSymbolicLatentPath F R γ).path⟩ := by
  apply Subtype.ext
  exact (mapSymbolicLatentPath_observed_start F γ).symm

theorem SymbolicLatentChartMorphism.observedPathImageMapTopCatHom_finish
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    F.observedPathImageMapTopCatHom R γ
        ⟨observedSymbolicLatentPath.finish C.system γ.path,
          observed_finish_mem_symbolicLatentPathImage C.system γ.path⟩ =
      ⟨observedSymbolicLatentPath.finish D.system
          (mapSymbolicLatentPath F R γ).path,
        observed_finish_mem_symbolicLatentPathImage D.system
          (mapSymbolicLatentPath F R γ).path⟩ := by
  apply Subtype.ext
  exact (mapSymbolicLatentPath_observed_finish F γ).symm

end InfoGeometry.Topology
