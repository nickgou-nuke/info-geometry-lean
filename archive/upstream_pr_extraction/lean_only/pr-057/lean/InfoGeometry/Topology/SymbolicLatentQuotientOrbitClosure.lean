import Mathlib
import InfoGeometry.Topology.SymbolicLatentQuotientFlowHomeomorph

namespace InfoGeometry.Topology

/-!
Topological orbit data after modular-flow quotient descent.

The closure statements are deliberately elementary: no compactness,
recurrence, minimality, or ergodicity is inferred from continuity alone.
-/

def SymbolicLatentFlowQuotient.orbit
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) : Set Q :=
  Set.range (fun t : ℝ => K.act t q)

def SymbolicLatentFlowQuotient.orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) : Set Q :=
  closure (K.orbit q)

theorem SymbolicLatentFlowQuotient.isClosed_orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    IsClosed (K.orbitClosure q) := by
  exact isClosed_closure

theorem SymbolicLatentFlowQuotient.orbit_subset_orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    K.orbit q ⊆ K.orbitClosure q := by
  exact subset_closure

theorem SymbolicLatentFlowQuotient.initial_mem_orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    q ∈ K.orbitClosure q := by
  apply K.orbit_subset_orbitClosure q
  exact ⟨0, K.act_zero q⟩

theorem SymbolicLatentFlowQuotient.actHomeomorph_image_orbit
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (s : ℝ) (q : Q) :
    K.actHomeomorph s '' K.orbit q =
      K.orbit (K.act s q) := by
  ext y
  constructor
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    change K.act t (K.act s q) = K.actHomeomorph s (K.act t q)
    rw [K.actHomeomorph_apply, ← K.act_add, ← K.act_add, add_comm]
  · rintro ⟨t, rfl⟩
    refine ⟨K.act t q, ⟨t, rfl⟩, ?_⟩
    change K.act s (K.act t q) = K.act t (K.act s q)
    rw [← K.act_add, ← K.act_add, add_comm]

theorem SymbolicLatentFlowQuotient.orbitClosure_mono
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    {q₁ q₂ : Q} (h : K.orbit q₁ ⊆ K.orbit q₂) :
    K.orbitClosure q₁ ⊆ K.orbitClosure q₂ := by
  exact closure_mono h

theorem SymbolicLatentFlowQuotient.actHomeomorph_image_orbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (s : ℝ) (q : Q) :
    K.actHomeomorph s '' K.orbitClosure q =
      K.orbitClosure (K.act s q) := by
  rw [SymbolicLatentFlowQuotient.orbitClosure,
    SymbolicLatentFlowQuotient.orbitClosure]
  rw [(K.actHomeomorph s).image_closure]
  exact congrArg closure (K.actHomeomorph_image_orbit s q)

end InfoGeometry.Topology
