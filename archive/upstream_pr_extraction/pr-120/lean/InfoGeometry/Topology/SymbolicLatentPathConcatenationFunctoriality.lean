import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathConcatenation
import InfoGeometry.Topology.SymbolicLatentPathFunctoriality

namespace InfoGeometry.Topology

/-!
# Functoriality of concatenation witnesses

Continuous maps transport the gluing data, including both half restrictions.
This is the categorical layer available before choosing a concrete piecewise
construction of concatenated paths.
-/

def mapSymbolicLatentPathConcatenation
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : X → Y) (hf : Continuous f)
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    SymbolicLatentPathConcatenation
      (mapSymbolicLatentPathContinuous f hf γ₀)
      (mapSymbolicLatentPathContinuous f hf γ₁) :=
  ⟨mapSymbolicLatentPathContinuous f hf C.path,
    ⟨by
      intro t
      exact congrArg f (C.first_half t), by
      intro t
      exact congrArg f (C.second_half t)⟩⟩

theorem mapSymbolicLatentPathConcatenation_compatible_endpoints
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : X → Y) (hf : Continuous f)
    (C : SymbolicLatentPathConcatenation γ₀ γ₁) :
    (mapSymbolicLatentPathContinuous f hf γ₀).finish =
      (mapSymbolicLatentPathContinuous f hf γ₁).start := by
  exact congrArg f C.compatible_endpoints

end InfoGeometry.Topology
