import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularFlow
import InfoGeometry.Topology.SymbolicLatentSpace

namespace InfoGeometry.Topology

def FiniteSymbolicLatentSystem.obs
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) : X → (ι → ℝ) :=
  symbolicObservationMap S

/-!
Observation-preserving modular flows.  Invariance of the readout is an
explicit field; it is not inferred from continuity or from the flow laws.
-/

structure SymbolicLatentObservableModularFlow
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    extends SymbolicLatentModularFlow X where
  preserves_observation : ∀ (t : ℝ) (x : X),
    S.obs (act t x) = S.obs x

theorem SymbolicLatentObservableModularFlow.observation_on_orbit
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    {x y : X} (hy : y ∈ Φ.toSymbolicLatentModularFlow.orbit x) :
    S.obs y = S.obs x := by
  rcases hy with ⟨t, rfl⟩
  exact Φ.preserves_observation t x

theorem SymbolicLatentObservableModularFlow.observation_coordinate_on_orbit
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    {x y : X} (hy : y ∈ Φ.toSymbolicLatentModularFlow.orbit x)
    (i : ι) :
    S.obs y i = S.obs x i := by
  exact congrFun (Φ.observation_on_orbit hy) i

theorem SymbolicLatentObservableModularFlow.observation_zero
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (x : X) :
    S.obs (Φ.act 0 x) = S.obs x := by
  exact Φ.preserves_observation 0 x

theorem SymbolicLatentObservableModularFlow.feasibleSet_preserved_forward
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) {x : X}
    (hx : x ∈ S.feasibleSet targets) :
    Φ.act t x ∈ S.feasibleSet targets := by
  intro i
  have hobs := congrFun (Φ.preserves_observation t x) i
  change (S.observable i) (Φ.act t x) =
    (S.observable i) x at hobs
  change (S.observable i) (Φ.act t x) ∈ targets i
  rw [hobs]
  exact hx i

theorem SymbolicLatentObservableModularFlow.feasibleSet_preserved_iff
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) (x : X) :
    Φ.act t x ∈ S.feasibleSet targets ↔
      x ∈ S.feasibleSet targets := by
  constructor
  · intro htx
    have hback := Φ.feasibleSet_preserved_forward targets (-t) htx
    have hinv : Φ.act (-t) (Φ.act t x) = x := by
      rw [← Φ.toSymbolicLatentModularFlow.add_apply]
      simpa using Φ.toSymbolicLatentModularFlow.zero_apply x
    simpa [hinv] using hback
  · exact Φ.feasibleSet_preserved_forward targets t

end InfoGeometry.Topology
