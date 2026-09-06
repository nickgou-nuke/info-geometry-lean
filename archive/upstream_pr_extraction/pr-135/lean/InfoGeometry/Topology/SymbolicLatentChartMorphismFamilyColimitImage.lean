import InfoGeometry.Topology.SymbolicLatentChartMorphismFamilyImageTopCat
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImage
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimitImageCompHaus

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open SymbolicLatentPathFamilyTopCatColimit
open SymbolicLatentPathFamilyTopCatColimitImage
open SymbolicLatentPathFamilyTopCatColimitImageCompHaus

/-!
# Naturality of the observed family colimit-image readout

The chart-morphism image map is compatible with the two corridor colimit
readouts.  This is the colimit-level naturality law for the jointly observed
family image; it does not identify the ambient feature spaces or add any
extra quotient structure.
-/

theorem SymbolicLatentChartMorphism.mapObservedPathFamilyTopCatColimitImageReadout_natural
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    observedSymbolicLatentPathFamilyTopCatColimitImageReadout
        C.system H (continuous_symbolicObservationMap C.system) ≫
        F.mapObservedPathFamilyImageTopCatHom H =
      observedSymbolicLatentPathFamilyTopCatColimitImageReadout
        D.system (F.mapPathFamily H)
          (continuous_symbolicObservationMap D.system) := by
  apply colimit.hom_ext
  intro i
  calc
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageReadout
          C.system H (continuous_symbolicObservationMap C.system) ≫
        F.mapObservedPathFamilyImageTopCatHom H =
      (observedSymbolicLatentPathFamilyImageCocone C.system H
          (continuous_symbolicObservationMap C.system)).ι.app i ≫
        F.mapObservedPathFamilyImageTopCatHom H := by
      rw [← Category.assoc,
        observedSymbolicLatentPathFamilyTopCatColimitImageReadout_stage]
    _ = (observedSymbolicLatentPathFamilyImageCocone D.system
          (F.mapPathFamily H) (continuous_symbolicObservationMap D.system)).ι.app i := by
      cases i with
      | initial =>
          change observedSymbolicLatentPathFamilyStartImageTopCatHom
              C.system H (continuous_symbolicObservationMap C.system) ≫
              F.mapObservedPathFamilyImageTopCatHom H =
            observedSymbolicLatentPathFamilyStartImageTopCatHom
              D.system (F.mapPathFamily H)
                (continuous_symbolicObservationMap D.system)
          rw [observedSymbolicLatentPathFamilyStartImageTopCatHom,
            Category.assoc,
            F.mapObservedPathFamilyImage_evaluation_factorization]
          rfl
      | extended =>
          exact F.mapObservedPathFamilyImage_evaluation_factorization H
    _ = colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
        observedSymbolicLatentPathFamilyTopCatColimitImageReadout
          D.system (F.mapPathFamily H)
            (continuous_symbolicObservationMap D.system) := by
      symm
      exact observedSymbolicLatentPathFamilyTopCatColimitImageReadout_stage
        D.system (F.mapPathFamily H)
          (continuous_symbolicObservationMap D.system) i

theorem SymbolicLatentChartMorphism.mapObservedPathFamilyCompHausColimitImageReadout_natural
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [T2Space Y] [CompactSpace P]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
        C.system H (continuous_symbolicObservationMap C.system) ≫
        compHausToTop.map (F.mapObservedPathFamilyImageCompHausHom H) =
      observedSymbolicLatentPathFamilyTopCatColimitImageCompHausReadout
        D.system (F.mapPathFamily H)
          (continuous_symbolicObservationMap D.system) := by
  change observedSymbolicLatentPathFamilyTopCatColimitImageReadout
      C.system H (continuous_symbolicObservationMap C.system) ≫
      F.mapObservedPathFamilyImageTopCatHom H =
    observedSymbolicLatentPathFamilyTopCatColimitImageReadout
      D.system (F.mapPathFamily H)
        (continuous_symbolicObservationMap D.system)
  exact F.mapObservedPathFamilyTopCatColimitImageReadout_natural H

end InfoGeometry.Topology
