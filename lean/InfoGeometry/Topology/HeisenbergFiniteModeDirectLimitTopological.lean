import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge

/-!
# Topological readout for the Heisenberg finite-mode direct-limit bridge

This file packages the verified finite-mode Heisenberg direct-limit bridge as
a topological readout. The topology is discrete on both source and target, so
continuity and local constancy are bookkeeping consequences of the algebraic
direct-limit transport.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological

open InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergFiniteModeDirectLimitTopologicalSpace :
    TopologicalSpace (heisenbergFiniteModeDirectLimit (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeDirectLimitDiscreteTopology :
    DiscreteTopology (heisenbergFiniteModeDirectLimit (𝕜 := 𝕜)) := ⟨rfl⟩

instance heisenbergFiniteModeDirectLimitTargetTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergFiniteModeDirectLimitTargetDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := ⟨rfl⟩

/-- The Heisenberg finite-mode direct-limit map, viewed as a topological readout. -/
def topologicalHeisenbergFiniteModeDirectLimitMap :
    heisenbergFiniteModeDirectLimit (𝕜 := 𝕜) → HeisenbergAlgebra 𝕜 :=
  fun x => (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom x

@[simp] theorem topologicalHeisenbergFiniteModeDirectLimitMap_eq :
    topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom := by
  rfl

/-- The finite-mode direct-limit Heisenberg map is continuous for the discrete topology. -/
theorem continuous_topologicalHeisenbergFiniteModeDirectLimitMap :
    Continuous (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeDirectLimitMap] using
    (continuous_of_discreteTopology :
      Continuous (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)))

/-- The direct-limit readout is algebraically exhaustive. -/
theorem surjective_topologicalHeisenbergFiniteModeDirectLimitMap :
    Function.Surjective
      (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeDirectLimitMap] using
    (heisenbergFiniteModeDirectLimitMap_surjective (𝕜 := 𝕜))

/-- The direct-limit readout is locally constant for the discrete topology. -/
theorem isLocallyConstant_topologicalHeisenbergFiniteModeDirectLimitMap :
    IsLocallyConstant (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeDirectLimitMap] using
    (IsLocallyConstant.of_discrete
      (f := topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)))

end
end InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological
