import Mathlib
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological

/-!
# Topological bridge from the Heisenberg boundary atlas to the Sugawara readout

This file packages the already verified Heisenberg boundary atlas together with
its current/Sugawara readout. It does not add a new current algebra or a new
boundary completion.

The bridge is purely packaging:

* the atlas packet is topological and discrete;
* the current Sugawara readout is recovered from the atlas's current
  Heisenberg representation;
* continuity and local constancy are bookkeeping consequences.
-/

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasCurrentSugawaraTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance boundaryAtlasSugawaraPacketTopologicalSpace :
    TopologicalSpace
      (Σ α : 𝕜,
        InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
          (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
            (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))) := ⊥

instance boundaryAtlasSugawaraPacketDiscreteTopology :
    DiscreteTopology
      (Σ α : 𝕜,
        InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
          (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
            (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))) := ⟨rfl⟩

/-- The Heisenberg boundary atlas together with its Sugawara readout. -/
def boundaryAtlasSugawaraPacket (α : 𝕜) :
    Σ α : 𝕜,
      InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
        (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
          (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  ⟨α,
    (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α,
      topologicalCurrentSugawaraReadout
        (𝕜 := 𝕜)
        (V := VirasoroProject.ChargedFockSpace 𝕜 α)
        (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α).currentRep)⟩

@[simp] theorem boundaryAtlasSugawaraPacket_fst (α : 𝕜) :
    (boundaryAtlasSugawaraPacket (𝕜 := 𝕜) α).1 = α := by
  rfl

@[simp] theorem boundaryAtlasSugawaraPacket_snd_fst (α : 𝕜) :
    (boundaryAtlasSugawaraPacket (𝕜 := 𝕜) α).2.1 =
      InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α := by
  rfl

@[simp] theorem boundaryAtlasSugawaraPacket_snd_snd (α : 𝕜) :
    (boundaryAtlasSugawaraPacket (𝕜 := 𝕜) α).2.2 =
      topologicalCurrentSugawaraReadout
        (𝕜 := 𝕜)
        (V := VirasoroProject.ChargedFockSpace 𝕜 α)
        (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α).currentRep := by
  rfl

/-- The boundary atlas current/Sugawara bridge is continuous on the discrete
parameter space. -/
theorem continuous_boundaryAtlasSugawaraPacket :
    Continuous (boundaryAtlasSugawaraPacket (𝕜 := 𝕜)) := by
  simpa [boundaryAtlasSugawaraPacket] using
    (continuous_of_discreteTopology :
      Continuous (boundaryAtlasSugawaraPacket (𝕜 := 𝕜)))

/-- The boundary atlas current/Sugawara bridge is locally constant on the
discrete parameter space. -/
theorem isLocallyConstant_boundaryAtlasSugawaraPacket :
    IsLocallyConstant (boundaryAtlasSugawaraPacket (𝕜 := 𝕜)) := by
  simpa [boundaryAtlasSugawaraPacket] using
    (IsLocallyConstant.of_discrete
      (f := boundaryAtlasSugawaraPacket (𝕜 := 𝕜)))

/-- The Sugawara central generator readout is preserved in the bridge packet. -/
theorem boundaryAtlasSugawaraPacket_currentSugawara_central
    (α : 𝕜) :
    (boundaryAtlasSugawaraPacket (𝕜 := 𝕜) α).2.2
        (VirasoroAlgebra.cgen 𝕜) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  simpa [boundaryAtlasSugawaraPacket] using
    (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_central
      (𝕜 := 𝕜) α)

/-- The `lgen` readout is preserved in the bridge packet. -/
theorem boundaryAtlasSugawaraPacket_currentSugawara_lgen_apply
    (α : 𝕜) (n : Int) :
    (boundaryAtlasSugawaraPacket (𝕜 := 𝕜) α).2.2
        (VirasoroAlgebra.lgen 𝕜 n) =
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.sugawaraStressMode
        ((InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α).currentRep)
        n := by
  simpa [boundaryAtlasSugawaraPacket] using
    (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_lgen_apply
      (𝕜 := 𝕜) α n)
