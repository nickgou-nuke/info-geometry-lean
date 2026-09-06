import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularFlow

namespace InfoGeometry.Topology

/-!
# Orbit closures of symbolic latent modular flows

This is the minimal topological asymptotic layer: an orbit closure is closed
and contains the orbit.  No compactness or recurrence claim is made without
additional hypotheses on the ambient space.
-/

def SymbolicLatentModularFlow.orbitClosure
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) : Set X :=
  closure (Φ.orbit x)

theorem SymbolicLatentModularFlow.isClosed_orbitClosure
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    IsClosed (Φ.orbitClosure x) := by
  exact isClosed_closure

theorem SymbolicLatentModularFlow.orbit_subset_orbitClosure
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.orbit x ⊆ Φ.orbitClosure x := by
  exact subset_closure

theorem SymbolicLatentModularFlow.initial_mem_orbitClosure
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    x ∈ Φ.orbitClosure x := by
  exact Φ.orbit_subset_orbitClosure x (Φ.orbit_mem x)

theorem SymbolicLatentModularFlow.orbitClosure_mono
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) {x y : X}
    (hxy : Φ.orbit x ⊆ Φ.orbit y) :
    Φ.orbitClosure x ⊆ Φ.orbitClosure y := by
  exact closure_mono hxy

end InfoGeometry.Topology
