import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientFunctoriality
import InfoGeometry.Topology.SymbolicLatentChartHomotopyBridge

namespace InfoGeometry.Topology

/-!
# Chart and observation maps on symbolic-latent homotopy classes

This is the quotient-level counterpart of the homotopy transport bridge.  The
underlying maps are the existing chart and observation continuous maps; all
well-definedness is inherited from the generic quotient owner.
-/

def SymbolicLatentChartMorphism.mapPathHomotopyQuotient
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) :
    SymbolicLatentPathHomotopyQuotient (X := X) →
      SymbolicLatentPathHomotopyQuotient (X := Y) :=
  mapSymbolicLatentPathHomotopyQuotient F.continuousMap

theorem SymbolicLatentChartMorphism.mapPathHomotopyQuotient_endpoint
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointMap
        (F.mapPathHomotopyQuotient q) =
      (fun p => (F.toFun p.1, F.toFun p.2))
        (symbolicLatentPathHomotopyEndpointMap q) :=
  mapSymbolicLatentPathHomotopyQuotient_endpoint F.continuousMap q

theorem SymbolicLatentChartMorphism.mapPathHomotopyQuotient_id
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι) :
    (SymbolicLatentChartMorphism.id C).mapPathHomotopyQuotient =
      (fun q : SymbolicLatentPathHomotopyQuotient (X := X) => q) := by
  simpa [SymbolicLatentChartMorphism.mapPathHomotopyQuotient,
    SymbolicLatentChartMorphism.id] using
    (mapSymbolicLatentPathHomotopyQuotient_id (X := X))

theorem SymbolicLatentChartMorphism.mapPathHomotopyQuotient_comp
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D) :
    (G.comp F).mapPathHomotopyQuotient =
      G.mapPathHomotopyQuotient ∘ F.mapPathHomotopyQuotient := by
  simpa [SymbolicLatentChartMorphism.mapPathHomotopyQuotient,
    SymbolicLatentChartMorphism.comp] using
    (mapSymbolicLatentPathHomotopyQuotient_comp
      (f := F.continuousMap) (g := G.continuousMap))

theorem SymbolicLatentChartMorphism.mapPathHomotopyQuotient_comp_apply
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartMorphism D E)
    (F : SymbolicLatentChartMorphism C D)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    (G.comp F).mapPathHomotopyQuotient q =
      G.mapPathHomotopyQuotient (F.mapPathHomotopyQuotient q) := by
  exact congrArg (fun h => h q)
    (SymbolicLatentChartMorphism.mapPathHomotopyQuotient_comp
      (G := G) (F := F))

def mapSymbolicObservationPathHomotopyQuotient
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    SymbolicLatentPathHomotopyQuotient (X := X) →
      SymbolicLatentPathHomotopyQuotient
        (X := SymbolicFeatureSpace ι) :=
  mapSymbolicLatentPathHomotopyQuotient
    (symbolicObservationContinuousMap S)

theorem mapSymbolicObservationPathHomotopyQuotient_endpoint
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointMap
        (mapSymbolicObservationPathHomotopyQuotient S q) =
      (fun p =>
        (symbolicObservationMap S p.1, symbolicObservationMap S p.2))
        (symbolicLatentPathHomotopyEndpointMap q) :=
  mapSymbolicLatentPathHomotopyQuotient_endpoint
    (symbolicObservationContinuousMap S) q

theorem mapSymbolicObservationPathHomotopyQuotient_id
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    mapSymbolicObservationPathHomotopyQuotient S =
      mapSymbolicLatentPathHomotopyQuotient
        (symbolicObservationContinuousMap S) :=
  rfl

end InfoGeometry.Topology
