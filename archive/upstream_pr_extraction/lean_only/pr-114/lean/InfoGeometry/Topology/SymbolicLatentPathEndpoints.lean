import Mathlib
import InfoGeometry.Topology.SymbolicLatentPath

namespace InfoGeometry.Topology

/-!
Endpoint API for the compact unit-interval model of symbolic latent paths.

This layer is deliberately independent of any algebraic multiplication.  A
path is a continuous map on `Icc 0 1`; its endpoints are therefore ordinary
evaluations, and chart transport acts on them by the same intertwining law as
on the whole path.
-/

def SymbolicLatentPath.start {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : X :=
  γ 0

def SymbolicLatentPath.finish {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : X :=
  γ 1

def SymbolicLatentPath.endpoints {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : X × X :=
  (γ.start, γ.finish)

theorem SymbolicLatentPath.start_mem_domain
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (0 : ℝ) ∈ SymbolicPathDomain := by
  constructor <;> norm_num

theorem SymbolicLatentPath.finish_mem_domain
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (1 : ℝ) ∈ SymbolicPathDomain := by
  constructor <;> norm_num

theorem SymbolicLatentPath.start_eq_apply_zero
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    γ.start = γ 0 := rfl

theorem SymbolicLatentPath.finish_eq_apply_one
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    γ.finish = γ 1 := rfl

theorem SymbolicLatentPath.endpoints_eq_apply
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    γ.endpoints = (γ 0, γ 1) := rfl

theorem SymbolicLatentPathInRegion.start_mem
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (γ : SymbolicLatentPathInRegion C R) :
    γ.path.start ∈ latentFeatureRegion C R :=
  γ.stays_in_region 0

theorem SymbolicLatentPathInRegion.finish_mem
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (γ : SymbolicLatentPathInRegion C R) :
    γ.path.finish ∈ latentFeatureRegion C R :=
  γ.stays_in_region 1

def observedSymbolicLatentPath.start
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) : ι → ℝ :=
  (symbolicObservationPath S γ) 0

def observedSymbolicLatentPath.finish
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) : ι → ℝ :=
  (symbolicObservationPath S γ) 1

def observedSymbolicLatentPath.endpoints
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) : (ι → ℝ) × (ι → ℝ) :=
  (observedSymbolicLatentPath.start S γ,
    observedSymbolicLatentPath.finish S γ)

theorem observedSymbolicLatentPath.start_eq_observe_start
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    observedSymbolicLatentPath.start S γ =
      symbolicObservationMap S γ.start := by
  rfl

theorem observedSymbolicLatentPath.finish_eq_observe_finish
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    observedSymbolicLatentPath.finish S γ =
      symbolicObservationMap S γ.finish := by
  rfl

theorem observedSymbolicLatentPath.endpoints_eq_observe_endpoints
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    observedSymbolicLatentPath.endpoints S γ =
      (symbolicObservationMap S γ.start,
        symbolicObservationMap S γ.finish) := by
  rfl

theorem mapSymbolicLatentPath_start
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    (mapSymbolicLatentPath F R γ).path.start = F.toFun γ.path.start := by
  rfl

theorem mapSymbolicLatentPath_finish
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    (mapSymbolicLatentPath F R γ).path.finish = F.toFun γ.path.finish := by
  rfl

theorem mapSymbolicLatentPath_endpoints
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    (mapSymbolicLatentPath F R γ).path.endpoints =
      (F.toFun γ.path.start, F.toFun γ.path.finish) := by
  rfl

theorem mapSymbolicLatentPath_observed_start
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    observedSymbolicLatentPath.start D.system (mapSymbolicLatentPath F R γ).path =
      F.featureMap (observedSymbolicLatentPath.start C.system γ.path) := by
  simpa [observedSymbolicLatentPath.start, observedPathInRegion] using
    (mapSymbolicLatentPath_observation F R γ 0)

theorem mapSymbolicLatentPath_observed_finish
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    observedSymbolicLatentPath.finish D.system (mapSymbolicLatentPath F R γ).path =
      F.featureMap (observedSymbolicLatentPath.finish C.system γ.path) := by
  simpa [observedSymbolicLatentPath.finish, observedPathInRegion] using
    (mapSymbolicLatentPath_observation F R γ 1)

theorem mapSymbolicLatentPath_observed_endpoints
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {R : Set (SymbolicFeatureSpace ι)}
    (F : SymbolicLatentChartMorphism C D)
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    observedSymbolicLatentPath.endpoints D.system
        (mapSymbolicLatentPath F R γ).path =
      (F.featureMap (observedSymbolicLatentPath.start C.system γ.path),
        F.featureMap (observedSymbolicLatentPath.finish C.system γ.path)) := by
  rw [observedSymbolicLatentPath.endpoints]
  rw [mapSymbolicLatentPath_observed_start F γ,
    mapSymbolicLatentPath_observed_finish F γ]

end InfoGeometry.Topology
