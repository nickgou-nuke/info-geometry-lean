import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamily

namespace InfoGeometry.Topology

/-!
Jointly continuous observed families.  Continuity of the observation map is
an explicit hypothesis, so this layer remains valid for arbitrary symbolic
latent systems whose readout regularity is supplied separately.
-/

def observedSymbolicLatentPathFamily
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    C(P × SymbolicPathDomain, ι → ℝ) := {
  toFun := fun q => symbolicObservationMap S (H q)
  continuous_toFun := h_obs.comp H.continuous
}

theorem observedSymbolicLatentPathFamily_apply
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (q : P × SymbolicPathDomain) :
    observedSymbolicLatentPathFamily S H h_obs q =
      symbolicObservationMap S (H q) := rfl

def observedSymbolicLatentPathFamilyImage
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) : Set (ι → ℝ) :=
  Set.range (observedSymbolicLatentPathFamily S H h_obs)

theorem isCompact_observedSymbolicLatentPathFamilyImage
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    IsCompact (observedSymbolicLatentPathFamilyImage S H h_obs) := by
  exact isCompact_range (observedSymbolicLatentPathFamily S H h_obs).continuous

theorem observedSymbolicLatentPathFamilyImage_subset
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S))
    (targets : ι → Set ℝ)
    (h_targets : ∀ q : P × SymbolicPathDomain, ∀ i : ι,
      symbolicObservationMap S (H q) i ∈ targets i) :
    observedSymbolicLatentPathFamilyImage S H h_obs ⊆
      {v : ι → ℝ | ∀ i, v i ∈ targets i} := by
  intro y hy
  rcases hy with ⟨q, rfl⟩
  intro i
  exact h_targets q i

end InfoGeometry.Topology
