import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathImage
import InfoGeometry.Topology.SymbolicLatentPathFunctoriality

namespace InfoGeometry.Topology

/-!
# Image transport for symbolic-latent paths

This owner records the set-level semantics of path transport.  It does not
introduce a homotopy relation: a transported path has exactly the image of the
original path under the ambient map.  The statement is useful for passing
compactness and feasibility certificates between latent and observed spaces.
-/

theorem symbolicLatentPathImage_map_eq_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathImage (mapSymbolicLatentPathContinuous f hf γ) =
      f '' symbolicLatentPathImage γ := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨γ t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

theorem isCompact_symbolicLatentPathImage_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (γ : SymbolicLatentPath X) :
    IsCompact (f '' symbolicLatentPathImage γ) := by
  rw [← symbolicLatentPathImage_map_eq_image f hf γ]
  exact isCompact_symbolicLatentPathImage
    (mapSymbolicLatentPathContinuous f hf γ)

theorem observedSymbolicLatentPathImage_eq_observation_image
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    observedSymbolicLatentPathImage S γ =
      symbolicObservationMap S '' symbolicLatentPathImage γ := by
  simpa [observedSymbolicLatentPathImage, symbolicLatentPathImage,
    symbolicObservationPath_apply] using
    (symbolicLatentPathImage_map_eq_image
      (symbolicObservationMap S)
      (continuous_symbolicObservationMap S) γ)

theorem isCompact_observedSymbolicLatentPathImage_as_observation_image
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    IsCompact (symbolicObservationMap S '' symbolicLatentPathImage γ) := by
  rw [← observedSymbolicLatentPathImage_eq_observation_image S γ]
  exact isCompact_observedSymbolicLatentPathImage S γ

theorem observedSymbolicLatentPathImage_subset_feasibleSet_of_stays
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain, ∀ i : ι,
      (symbolicObservationPath S γ) t i ∈ targets i) :
    symbolicObservationMap S '' symbolicLatentPathImage γ ⊆
      {v | ∀ i, v i ∈ targets i} := by
  rw [← observedSymbolicLatentPathImage_eq_observation_image S γ]
  exact observedSymbolicLatentPathImage_subset_feasibleSet S targets γ hγ

end InfoGeometry.Topology
