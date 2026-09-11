import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FibonacciGrothendieckLimit

/-!
# Topological readout for the Fibonacci Grothendieck limit

This file packages the existing additive direct-limit `L₀` lift from
`InfoGeometry.Canonical.FibonacciGrothendieckLimit` as a topological readout.
The topology is intentionally discrete on the source colimit, so the continuity
statement is bookkeeping only: it records that the canonical direct-limit
transport can be viewed as a continuous map.
-/

namespace InfoGeometry.Topology.FibonacciGrothendieckLimitTopological

open InfoGeometry.Canonical.FibonacciGrothendieckLimit

noncomputable section

variable {u : Level}
variable {𝕜 V : Type u} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

instance fibFusionGrothendieckColimitTopologicalSpace :
    TopologicalSpace fibFusionGrothendieckColimit := ⊥

instance fibFusionGrothendieckColimitDiscreteTopology :
    DiscreteTopology fibFusionGrothendieckColimit := ⟨rfl⟩

instance endTopologicalSpace : TopologicalSpace (V →ₗ[𝕜] V) := ⊥

instance endDiscreteTopology : DiscreteTopology (V →ₗ[𝕜] V) := ⟨rfl⟩

/-- The additive Fibonacci Grothendieck `L₀` lift, viewed as a topological map. -/
def topologicalFibFusionLZeroLift (L : V →ₗ[𝕜] V) :
    fibFusionGrothendieckColimit → (V →ₗ[𝕜] V) :=
  fibFusionLZeroLift (𝕜 := 𝕜) (V := V) L

@[simp] theorem topologicalFibFusionLZeroLift_eq
    (L : V →ₗ[𝕜] V) :
    topologicalFibFusionLZeroLift (𝕜 := 𝕜) (V := V) L =
      fibFusionLZeroLift (𝕜 := 𝕜) (V := V) L := by
  rfl

/-- The Fibonacci Grothendieck `L₀` lift is continuous for the discrete topology. -/
theorem continuous_topologicalFibFusionLZeroLift (L : V →ₗ[𝕜] V) :
    Continuous (topologicalFibFusionLZeroLift (𝕜 := 𝕜) (V := V) L) := by
  simpa [topologicalFibFusionLZeroLift] using
    (continuous_of_discreteTopology :
      Continuous (fibFusionLZeroLift (𝕜 := 𝕜) (V := V) L))

/-- The Fibonacci Grothendieck `L₀` lift is locally constant for the discrete topology. -/
theorem isLocallyConstant_topologicalFibFusionLZeroLift (L : V →ₗ[𝕜] V) :
    IsLocallyConstant (topologicalFibFusionLZeroLift (𝕜 := 𝕜) (V := V) L) := by
  simpa [topologicalFibFusionLZeroLift] using
    (IsLocallyConstant.of_discrete (f := fibFusionLZeroLift (𝕜 := 𝕜) (V := V) L))

end
end InfoGeometry.Topology.FibonacciGrothendieckLimitTopological
