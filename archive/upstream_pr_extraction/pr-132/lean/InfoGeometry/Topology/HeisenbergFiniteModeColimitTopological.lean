import Mathlib
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit

/-!
# Topological readout for the finite-mode Heisenberg colimit

This file packages the existing finite-mode colimit map from
`InfoGeometry.Canonical.HeisenbergFiniteModeColimit` as a topological readout.
The topology is intentionally discrete on the source colimit and on the target
Heisenberg algebra object, so continuity and local constancy are bookkeeping
consequences of the already proved algebraic colimit transport.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological

open InfoGeometry.Canonical
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergFiniteModeColimitTopologicalSpace :
    TopologicalSpace (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeColimitDiscreteTopology :
    DiscreteTopology (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := ⟨rfl⟩

instance heisenbergAlgebraTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergAlgebraDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := ⟨rfl⟩

/-- The finite-mode Heisenberg colimit map, viewed as a topological readout. -/
def topologicalHeisenbergFiniteModeColimitMap :
    heisenbergFiniteModeColimit (𝕜 := 𝕜) → HeisenbergAlgebra 𝕜 :=
  fun x => (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom x

@[simp] theorem topologicalHeisenbergFiniteModeColimitMap_eq :
    topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  rfl

/-- The finite-mode Heisenberg colimit map is continuous for the discrete topology. -/
theorem continuous_topologicalHeisenbergFiniteModeColimitMap :
    Continuous (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeColimitMap] using
    (continuous_of_discreteTopology :
      Continuous (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)))

/-- The topological readout is algebraically exhaustive: every current is
represented by a finite-mode stage.  No injectivity or analytic completion is
asserted here. -/
theorem surjective_topologicalHeisenbergFiniteModeColimitMap :
    Function.Surjective
      (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeColimitMap] using
    (heisenbergFiniteModeColimitMap_surjective (𝕜 := 𝕜))

/-- The finite-mode Heisenberg colimit map is locally constant for the
discrete topology. -/
theorem isLocallyConstant_topologicalHeisenbergFiniteModeColimitMap :
    IsLocallyConstant (topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeColimitMap] using
    (IsLocallyConstant.of_discrete
      (f := topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜)))

end
end InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological
