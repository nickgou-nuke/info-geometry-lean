import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

namespace InfoGeometry.Topology

/-!
Compact image semantics for symbolic latent paths.  The parameter domain is
the compact unit interval, so every continuous latent trajectory and every
finite observation trajectory has compact range.
-/

def symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : Set X :=
  Set.range γ

theorem isCompact_symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    IsCompact (symbolicLatentPathImage γ) := by
  exact isCompact_range γ.continuous

theorem isClosed_symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    [T2Space X]
    (γ : SymbolicLatentPath X) :
    IsClosed (symbolicLatentPathImage γ) :=
  (isCompact_symbolicLatentPathImage γ).isClosed

theorem start_mem_symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    γ.start ∈ symbolicLatentPathImage γ := by
  exact ⟨0, rfl⟩

theorem finish_mem_symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    γ.finish ∈ symbolicLatentPathImage γ := by
  exact ⟨1, rfl⟩

theorem nonempty_symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    (symbolicLatentPathImage γ).Nonempty := by
  exact ⟨γ.start, start_mem_symbolicLatentPathImage γ⟩

def observedSymbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) : Set (ι → ℝ) :=
  Set.range (symbolicObservationPath S γ)

theorem isCompact_observedSymbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    IsCompact (observedSymbolicLatentPathImage S γ) := by
  exact isCompact_range (symbolicObservationPath S γ).continuous

theorem isClosed_observedSymbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    IsClosed (observedSymbolicLatentPathImage S γ) :=
  (isCompact_observedSymbolicLatentPathImage S γ).isClosed

theorem observed_start_mem_symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    observedSymbolicLatentPath.start S γ ∈
      observedSymbolicLatentPathImage S γ := by
  exact ⟨0, rfl⟩

theorem observed_finish_mem_symbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    observedSymbolicLatentPath.finish S γ ∈
      observedSymbolicLatentPathImage S γ := by
  exact ⟨1, rfl⟩

theorem nonempty_observedSymbolicLatentPathImage
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    (observedSymbolicLatentPathImage S γ).Nonempty := by
  exact ⟨observedSymbolicLatentPath.start S γ,
    observed_start_mem_symbolicLatentPathImage S γ⟩

theorem observedSymbolicLatentPathImage_subset_feasibleSet
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (targets : ι → Set ℝ)
    (γ : SymbolicLatentPath X)
    (hγ : ∀ t : SymbolicPathDomain,
      ∀ i : ι, (symbolicObservationPath S γ) t i ∈ targets i) :
    observedSymbolicLatentPathImage S γ ⊆
      {v | ∀ i, v i ∈ targets i} := by
  intro y hy
  rcases hy with ⟨t, rfl⟩
  intro i
  exact hγ t i

end InfoGeometry.Topology
