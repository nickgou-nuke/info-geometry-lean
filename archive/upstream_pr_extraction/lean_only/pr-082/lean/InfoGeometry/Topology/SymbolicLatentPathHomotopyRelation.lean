import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopy

namespace InfoGeometry.Topology

/-!
Canonical reflexive homotopies.  Symmetry and transitivity are intentionally
left to a later reparametrisation/gluing layer; they are not consequences of
the endpoint data alone.
-/

def constantSymbolicLatentPathHomotopy
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPathHomotopy γ γ where
  map := {
    toFun := fun p => γ p.2
    continuous_toFun := γ.continuous.comp continuous_snd
  }
  at_start := by
    intro t
    rfl
  at_finish := by
    intro t
    rfl
  fixed_start := by
    intro s
    rfl
  fixed_finish := by
    intro s
    rfl

theorem SymbolicLatentPathHomotopic.refl
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPathHomotopic γ γ :=
  ⟨constantSymbolicLatentPathHomotopy γ⟩

theorem SymbolicLatentPathHomotopic.endpoint_invariant
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    γ₀.start = γ₁.start ∧ γ₀.finish = γ₁.finish := by
  rcases h with ⟨H⟩
  exact ⟨H.same_start, H.same_finish⟩

end InfoGeometry.Topology
