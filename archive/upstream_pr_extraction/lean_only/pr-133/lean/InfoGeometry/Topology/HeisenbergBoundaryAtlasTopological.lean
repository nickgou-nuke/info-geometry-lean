import Mathlib
import InfoGeometry.Canonical.HeisenbergBoundaryAtlas

/-!
# Topological readout for the Heisenberg boundary atlas

This file packages the already-verified Heisenberg boundary atlas as a
topological readout. The parameter space and atlas carrier are given discrete
topologies, so continuity and local constancy are bookkeeping consequences of
the algebraic atlas fields.
-/

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological

open InfoGeometry.Canonical
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-! The parameter space and the total atlas packet are both given discrete
topologies. This keeps the packaging honest while avoiding dependent-codomain
continuity claims. -/
instance heisenbergBoundaryAtlasParameterTopologicalSpace :
    TopologicalSpace 𝕜 := ⊥

instance heisenbergBoundaryAtlasParameterDiscreteTopology :
    DiscreteTopology 𝕜 := ⟨rfl⟩

/-- Total-space packet for the parameterized Heisenberg boundary atlas. -/
abbrev HeisenbergBoundaryAtlasPacket :=
  Σ α : 𝕜, InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α

instance heisenbergBoundaryAtlasPacketTopologicalSpace :
    TopologicalSpace (HeisenbergBoundaryAtlasPacket (𝕜 := 𝕜)) := ⊥

instance heisenbergBoundaryAtlasPacketDiscreteTopology :
    DiscreteTopology (HeisenbergBoundaryAtlasPacket (𝕜 := 𝕜)) := ⟨rfl⟩

/-- The Heisenberg boundary atlas, viewed as a topological packet. -/
def topologicalHeisenbergBoundaryAtlas :
    𝕜 → HeisenbergBoundaryAtlasPacket (𝕜 := 𝕜) :=
  fun α => ⟨α, InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas
    (𝕜 := 𝕜) α⟩

@[simp] theorem topologicalHeisenbergBoundaryAtlas_eq
    (α : 𝕜) :
    topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α =
      ⟨α, InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α⟩ := by
  rfl

/-- The Heisenberg boundary atlas readout is continuous on the discrete
parameter space. -/
theorem continuous_topologicalHeisenbergBoundaryAtlas :
    Continuous (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergBoundaryAtlas] using
    (continuous_of_discreteTopology :
      Continuous (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜)))

/-- The Heisenberg boundary atlas readout is locally constant on the discrete
parameter space. -/
theorem isLocallyConstant_topologicalHeisenbergBoundaryAtlas :
    IsLocallyConstant (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergBoundaryAtlas] using
    (IsLocallyConstant.of_discrete
      (f := topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜)))

end
end InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
