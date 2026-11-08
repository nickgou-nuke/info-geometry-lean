import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartMorphismFamily
import InfoGeometry.Topology.SymbolicLatentObservedFamilyImageTopCat
import InfoGeometry.Topology.SymbolicLatentChartMorphismTopCat
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageCompHaus

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transport for jointly observed chart-morphism families

The chart-morphism feature map restricts to the jointly observed family
images.  This owner records the induced subtype map and its two canonical
factorizations: through family evaluation and through the ambient feature
space.
-/

def SymbolicLatentChartMorphism.mapObservedPathFamilyImageTopCatHom
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (observedSymbolicLatentPathFamilyImage C.system H
      (continuous_symbolicObservationMap C.system)) ⟶
      TopCat.of (observedSymbolicLatentPathFamilyImage D.system
        (F.mapPathFamily H) (continuous_symbolicObservationMap D.system)) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨F.featureMap y.1, by
          rcases y.property with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          change (observedSymbolicLatentPathFamily D.system
            (F.mapPathFamily H) (continuous_symbolicObservationMap D.system)) q =
            F.featureMap y.1
          rw [← hq]
          exact F.mapPathFamily_observation H q⟩
      continuous_toFun :=
        (F.continuous_featureMap.comp continuous_subtype_val).subtype_mk
          (fun y => by
            rcases y.property with ⟨q, hq⟩
            refine ⟨q, ?_⟩
            change (observedSymbolicLatentPathFamily D.system
              (F.mapPathFamily H) (continuous_symbolicObservationMap D.system)) q =
              F.featureMap y.1
            rw [← hq]
            exact F.mapPathFamily_observation H q) }

@[simp] theorem SymbolicLatentChartMorphism.mapObservedPathFamilyImageTopCatHom_apply
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X)
    (y : observedSymbolicLatentPathFamilyImage C.system H
      (continuous_symbolicObservationMap C.system)) :
    F.mapObservedPathFamilyImageTopCatHom H y =
      ⟨F.featureMap y.1, by
        rcases y.property with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [← hq]
        exact F.mapPathFamily_observation H q⟩ := rfl

theorem SymbolicLatentChartMorphism.mapObservedPathFamilyImage_evaluation_factorization
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    observedSymbolicLatentPathFamilyImageEvaluationTopCatHom C.system H
        (continuous_symbolicObservationMap C.system) ≫
        F.mapObservedPathFamilyImageTopCatHom H =
      observedSymbolicLatentPathFamilyImageEvaluationTopCatHom D.system
        (F.mapPathFamily H) (continuous_symbolicObservationMap D.system) := by
  apply TopCat.hom_ext
  ext q i
  exact congrFun (F.mapPathFamily_observation H q).symm i

theorem SymbolicLatentChartMorphism.mapObservedPathFamilyImage_inclusion_natural
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    F.mapObservedPathFamilyImageTopCatHom H ≫
        observedSymbolicLatentPathFamilyImageInclusionTopCatHom D.system
          (F.mapPathFamily H) (continuous_symbolicObservationMap D.system) =
      observedSymbolicLatentPathFamilyImageInclusionTopCatHom C.system H
          (continuous_symbolicObservationMap C.system) ≫
        F.featureMapTopCatHom := by
  ext y i
  rfl

theorem SymbolicLatentChartMorphism.mapObservedPathFamilyImageTopCatHom_comp
    {P X Y Z : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    F.mapObservedPathFamilyImageTopCatHom H ≫
        G.mapObservedPathFamilyImageTopCatHom (F.mapPathFamily H) =
      (G.comp F).mapObservedPathFamilyImageTopCatHom H := by
  ext q
  rfl

noncomputable def SymbolicLatentChartMorphism.mapObservedPathFamilyImageCompHausHom
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace P]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    observedSymbolicLatentPathFamilyImageCompHaus C.system H
        (continuous_symbolicObservationMap C.system) ⟶
      observedSymbolicLatentPathFamilyImageCompHaus D.system
        (F.mapPathFamily H) (continuous_symbolicObservationMap D.system) := by
  letI : CompactSpace
      (observedSymbolicLatentPathFamilyImage C.system H
        (continuous_symbolicObservationMap C.system)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_observedSymbolicLatentPathFamilyImage C.system H
        (continuous_symbolicObservationMap C.system))
  letI : CompactSpace
      (observedSymbolicLatentPathFamilyImage D.system (F.mapPathFamily H)
        (continuous_symbolicObservationMap D.system)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_observedSymbolicLatentPathFamilyImage D.system
        (F.mapPathFamily H) (continuous_symbolicObservationMap D.system))
  change CompHaus.of (observedSymbolicLatentPathFamilyImage C.system H
      (continuous_symbolicObservationMap C.system)) ⟶
    CompHaus.of (observedSymbolicLatentPathFamilyImage D.system
      (F.mapPathFamily H) (continuous_symbolicObservationMap D.system))
  exact ⟨F.mapObservedPathFamilyImageTopCatHom H⟩

theorem SymbolicLatentChartMorphism.mapObservedPathFamilyImageCompHausHom_forget
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace P]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    compHausToTop.map (F.mapObservedPathFamilyImageCompHausHom H) =
      F.mapObservedPathFamilyImageTopCatHom H := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem SymbolicLatentChartMorphism.mapObservedPathFamilyImageCompHausHom_comp
    {P X Y Z : Type} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    F.mapObservedPathFamilyImageCompHausHom H ≫
        G.mapObservedPathFamilyImageCompHausHom (F.mapPathFamily H) =
      (G.comp F).mapObservedPathFamilyImageCompHausHom H := by
  ext x
  rfl

end InfoGeometry.Topology
