import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathHomotopyFunctoriality
import InfoGeometry.Topology.SymbolicLatentChartMorphism

namespace InfoGeometry.Topology

/-!
# Chart and observation specializations of homotopy functoriality

These are direct instances of the generic continuous-map transport theorem.
The chart intertwining law is retained by the existing chart owner; this file
only transports the topological homotopy property.
-/

def SymbolicLatentChartMorphism.continuousMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) : C(X, Y) :=
  { toFun := F.toFun
    continuous_toFun := F.continuous_toFun }

@[simp] theorem SymbolicLatentChartMorphism.continuousMap_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) (x : X) :
    F.continuousMap x = F.toFun x :=
  rfl

theorem SymbolicLatentChartMorphism.mapPathHomotopic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    SymbolicLatentPathHomotopic
      (F.continuousMap.comp γ₀) (F.continuousMap.comp γ₁) := by
  exact mapSymbolicLatentPathHomotopic F.continuousMap h

theorem SymbolicLatentChartMorphism.mapPath_start
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPath.start (F.continuousMap.comp γ) = F.toFun γ.start :=
  rfl

theorem SymbolicLatentChartMorphism.mapPath_finish
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPath.finish (F.continuousMap.comp γ) = F.toFun γ.finish :=
  rfl

def symbolicObservationContinuousMap
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    C(X, SymbolicFeatureSpace ι) :=
  { toFun := symbolicObservationMap S
    continuous_toFun := continuous_symbolicObservationMap S }

@[simp] theorem symbolicObservationContinuousMap_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (x : X) :
    symbolicObservationContinuousMap S x = symbolicObservationMap S x :=
  rfl

theorem symbolicObservationMapPathHomotopic
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    SymbolicLatentPathHomotopic
      ((symbolicObservationContinuousMap S).comp γ₀)
      ((symbolicObservationContinuousMap S).comp γ₁) := by
  exact mapSymbolicLatentPathHomotopic (symbolicObservationContinuousMap S) h

theorem symbolicObservationMapPath_start
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (γ : SymbolicLatentPath X) :
    SymbolicLatentPath.start ((symbolicObservationContinuousMap S).comp γ) =
      symbolicObservationMap S γ.start :=
  rfl

theorem symbolicObservationMapPath_finish
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (γ : SymbolicLatentPath X) :
    SymbolicLatentPath.finish ((symbolicObservationContinuousMap S).comp γ) =
      symbolicObservationMap S γ.finish :=
  rfl

end InfoGeometry.Topology
