import InfoGeometry.Topology.SymbolicLatentModularFlow
import InfoGeometry.Physics.TomitaTakesakiModularFlow

/-!
# Symbolic-latent modular flow: algebraic transport bridge

The topological symbolic-latent flow records continuity and the additive flow
law.  This file transports exactly those laws to the existing algebraic
`ModularFlowData` interface when the carrier is also a ring.  No KMS state,
Hilbert-space representation, or von Neumann closure is asserted here.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Physics

def SymbolicLatentModularFlow.toModularFlowData
    {X : Type*} [Ring X] [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) :
    ModularFlowData X where
  sigma := Φ.act
  sigma_zero := Φ.zero_apply
  sigma_add := Φ.add_apply
  sigma_neg_left := by
    intro t x
    simpa [Φ.zero_apply] using (Φ.add_apply (-t) t x).symm
  sigma_neg_right := by
    intro t x
    simpa [Φ.zero_apply] using (Φ.add_apply t (-t) x).symm

theorem SymbolicLatentModularFlow.toModularFlowData_bijective
    {X : Type*} [Ring X] [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    Function.Bijective (Φ.act t) := by
  exact modular_flow_is_bijective X Φ.toModularFlowData t

theorem SymbolicLatentModularFlow.toModularFlowData_group_law
    {X : Type*} [Ring X] [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) (x : X) :
    Φ.act (s + t) x = Φ.act s (Φ.act t x) :=
  Φ.add_apply s t x

@[simp] theorem SymbolicLatentModularFlow.toModularFlowData_sigma_zero
    {X : Type*} [Ring X] [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    (Φ.toModularFlowData).sigma 0 x = x := by
  simpa [SymbolicLatentModularFlow.toModularFlowData] using Φ.zero_apply x

@[simp] theorem SymbolicLatentModularFlow.toModularFlowData_sigma_add
    {X : Type*} [Ring X] [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) (x : X) :
    (Φ.toModularFlowData).sigma (s + t) x =
      (Φ.toModularFlowData).sigma s ((Φ.toModularFlowData).sigma t x) := by
  simpa [SymbolicLatentModularFlow.toModularFlowData] using
      Φ.add_apply s t x

@[simp] theorem SymbolicLatentModularFlow.toModularFlowData_sigma_neg_left
    {X : Type*} [Ring X] [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    (Φ.toModularFlowData).sigma (-t) ((Φ.toModularFlowData).sigma t x) = x := by
  calc
    (Φ.toModularFlowData).sigma (-t) ((Φ.toModularFlowData).sigma t x) =
        (Φ.toModularFlowData).sigma 0 x := by
          simpa [SymbolicLatentModularFlow.toModularFlowData] using
              (Φ.add_apply (-t) t x).symm
    _ = x := by
      simpa [SymbolicLatentModularFlow.toModularFlowData] using Φ.zero_apply x

@[simp] theorem SymbolicLatentModularFlow.toModularFlowData_sigma_neg_right
    {X : Type*} [Ring X] [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    (Φ.toModularFlowData).sigma t ((Φ.toModularFlowData).sigma (-t) x) = x := by
  calc
    (Φ.toModularFlowData).sigma t ((Φ.toModularFlowData).sigma (-t) x) =
        (Φ.toModularFlowData).sigma 0 x := by
          simpa [SymbolicLatentModularFlow.toModularFlowData] using
              (Φ.add_apply t (-t) x).symm
    _ = x := by
      simpa [SymbolicLatentModularFlow.toModularFlowData] using Φ.zero_apply x

end InfoGeometry.Topology
