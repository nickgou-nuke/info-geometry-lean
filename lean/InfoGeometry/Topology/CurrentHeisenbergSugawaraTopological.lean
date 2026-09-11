import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Topological readout for the current Heisenberg/Sugawara corridor

This file packages the existing `CurrentHeisenbergRep` → Sugawara transport
as a topological readout. The source carrier is given the discrete topology,
so continuity and local constancy are bookkeeping consequences of the already
proved algebraic bridge.
-/

namespace InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological

open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

noncomputable section

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

instance currentHeisenbergRepTopologicalSpace :
    TopologicalSpace (CurrentHeisenbergRep 𝕜 V) := ⊥

instance currentHeisenbergRepDiscreteTopology :
    DiscreteTopology (CurrentHeisenbergRep 𝕜 V) := ⟨rfl⟩

instance currentSugawaraMorphismTopologicalSpace :
    TopologicalSpace (VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) := ⊥

instance currentSugawaraMorphismDiscreteTopology :
    DiscreteTopology (VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) := ⟨rfl⟩

/-- The Sugawara readout attached to a current Heisenberg representation. -/
def topologicalCurrentSugawaraReadout (H : CurrentHeisenbergRep 𝕜 V) :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  H.currentSugawaraRepresentation

@[simp] theorem topologicalCurrentSugawaraReadout_eq (H : CurrentHeisenbergRep 𝕜 V) :
    topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V) H =
      H.currentSugawaraRepresentation := by
  rfl

/-- The Sugawara readout is continuous for the discrete topology on the source. -/
theorem continuous_topologicalCurrentSugawaraReadout :
    Continuous (topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V)) := by
  simpa [topologicalCurrentSugawaraReadout] using
    (continuous_of_discreteTopology :
      Continuous (topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V)))

/-- The Sugawara readout is locally constant for the discrete topology on the source. -/
theorem isLocallyConstant_topologicalCurrentSugawaraReadout :
    IsLocallyConstant (topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V)) := by
  simpa [topologicalCurrentSugawaraReadout] using
    (IsLocallyConstant.of_discrete
      (f := topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V)))

end
end InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological
