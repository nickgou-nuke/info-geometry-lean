import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentAtlas

/-!
# Paths in symbolic latent spaces

Paths are bundled as `ContinuousMap`s on the compact interval.  The only
claim made here is continuous transport through the observation map and
membership preservation for paths constrained to a feature region.
-/

namespace InfoGeometry.Topology

abbrev SymbolicPathDomain := Set.Icc (0 : ℝ) 1

abbrev SymbolicLatentPath
    (X : Type*) [TopologicalSpace X] :=
  C(SymbolicPathDomain, X)

def symbolicObservationPath
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    C(SymbolicPathDomain, SymbolicFeatureSpace ι) where
  toFun := fun t => symbolicObservationMap S (γ t)
  continuous_toFun :=
    (continuous_symbolicObservationMap S).comp γ.continuous

@[simp] theorem symbolicObservationPath_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    symbolicObservationPath S γ t = symbolicObservationMap S (γ t) :=
  rfl

abbrev SymbolicLatentPathInRegion
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι)
    (R : Set (SymbolicFeatureSpace ι)) :=
  {γ : SymbolicLatentPath X // ∀ t, γ t ∈ latentFeatureRegion C R}

namespace SymbolicLatentPathInRegion

abbrev path
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (γ : SymbolicLatentPathInRegion C R) : SymbolicLatentPath X := γ.1

abbrev stays_in_region
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (γ : SymbolicLatentPathInRegion C R) :
    ∀ t, γ.path t ∈ latentFeatureRegion C R := γ.2

end SymbolicLatentPathInRegion

def observedPathInRegion
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (γ : SymbolicLatentPathInRegion C R) :
    C(SymbolicPathDomain, SymbolicFeatureSpace ι) :=
  symbolicObservationPath C.system γ.path

theorem observedPath_stays_in_featureRegion
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (γ : SymbolicLatentPathInRegion C R)
    (t : SymbolicPathDomain) :
    observedPathInRegion γ t ∈ R := by
  change symbolicObservationMap C.system (γ.path t) ∈ R
  exact γ.stays_in_region t

def mapSymbolicLatentPath
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    SymbolicLatentPathInRegion D R :=
  ⟨{ toFun := fun t => F.toFun (γ.path t),
      continuous_toFun := F.continuous_toFun.comp γ.path.continuous }, by
    intro t
    exact F.map_latentFeatureRegion R
      ⟨γ.path t, γ.stays_in_region t, rfl⟩⟩

theorem mapSymbolicLatentPath_observation
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R))
    (t : SymbolicPathDomain) :
    observedPathInRegion (mapSymbolicLatentPath F R γ) t =
      F.featureMap (observedPathInRegion γ t) := by
  change symbolicObservationMap D.system (F.toFun (γ.path t)) =
    F.featureMap (symbolicObservationMap C.system (γ.path t))
  rw [← F.intertwines]

end InfoGeometry.Topology
