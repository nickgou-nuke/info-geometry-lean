import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

/-!
# Continuous-map transport of symbolic latent observation paths

The pointwise chart-morphism intertwining law already transports every path
observation.  This owner packages that law as equality of bundled continuous
maps, so later image, compactness, and categorical constructions can reuse it
without reopening coordinates.
-/

namespace InfoGeometry.Topology

def SymbolicLatentChartMorphism.featureMapContinuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D) :
    C(SymbolicFeatureSpace ι, SymbolicFeatureSpace ι) :=
  ⟨F.featureMap, F.continuous_featureMap⟩

@[simp] theorem SymbolicLatentChartMorphism.featureMapContinuous_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (z : SymbolicFeatureSpace ι) :
    F.featureMapContinuous z = F.featureMap z := rfl

theorem SymbolicLatentChartMorphism.mapSymbolicLatentPath_observedPath_eq_comp
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (R : Set (SymbolicFeatureSpace ι))
    (γ : SymbolicLatentPathInRegion C (F.featureMap ⁻¹' R)) :
    observedPathInRegion (mapSymbolicLatentPath F R γ) =
      F.featureMapContinuous.comp (observedPathInRegion γ) := by
  apply ContinuousMap.ext
  intro t
  change observedPathInRegion (mapSymbolicLatentPath F R γ) t =
    F.featureMap (observedPathInRegion γ t)
  exact mapSymbolicLatentPath_observation F R γ t

end InfoGeometry.Topology
