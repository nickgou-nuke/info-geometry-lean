import Mathlib
import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
import InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological

/-!
# Topological bridge for the Heisenberg boundary atlas, sixth-root lane, and
current Sugawara readout

This owner packages three already-verified surfaces:

* the Heisenberg boundary atlas with its finite-mode readout;
* the sixth-root cyclotomic parameter lane;
* the current Heisenberg/Sugawara readout on the charged Fock space.

It does not claim any new identification between these carriers.  The bridge is
purely a discrete topological packet.
-/

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergCyclotomicParameterTopologicalSpace :
    TopologicalSpace 𝕜 := ⊥

instance heisenbergCyclotomicParameterDiscreteTopology :
    DiscreteTopology 𝕜 := ⟨rfl⟩

instance heisenbergCyclotomicSugawaraInputTopologicalSpace :
    TopologicalSpace (𝕜 × SixthRootParameter) := ⊥

instance heisenbergCyclotomicSugawaraInputDiscreteTopology :
    DiscreteTopology (𝕜 × SixthRootParameter) := ⟨rfl⟩

abbrev BoundaryAtlasCyclotomicSugawaraPacket :=
  Σ α : 𝕜,
    SixthRootParameter ×
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.Atlas (𝕜 := 𝕜) α ×
        (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
          (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)))

instance boundaryAtlasCyclotomicSugawaraPacketTopologicalSpace :
    TopologicalSpace (BoundaryAtlasCyclotomicSugawaraPacket (𝕜 := 𝕜)) := ⊥

instance boundaryAtlasCyclotomicSugawaraPacketDiscreteTopology :
    DiscreteTopology (BoundaryAtlasCyclotomicSugawaraPacket (𝕜 := 𝕜)) := ⟨rfl⟩

/-- The combined Heisenberg boundary / sixth-root / Sugawara readout. -/
def boundaryAtlasCyclotomicSugawaraReadout
    (p : 𝕜 × SixthRootParameter) :
    BoundaryAtlasCyclotomicSugawaraPacket (𝕜 := 𝕜) :=
  ⟨p.1,
    (p.2,
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
        (𝕜 := 𝕜) p.1 p.2.1 p.2.2,
        topologicalCurrentSugawaraReadout
          (𝕜 := 𝕜)
          (V := VirasoroProject.ChargedFockSpace 𝕜 p.1)
          (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
            (𝕜 := 𝕜) p.1 p.2.1 p.2.2).heisenberg.currentRep))⟩

@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_fst
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).1 = p.1 := by
  rfl

@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_snd_fst
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.1 = p.2 := by
  rfl

@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_snd_snd_fst
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.1 =
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
        (𝕜 := 𝕜) p.1 p.2.1 p.2.2) := by
  rfl

@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_snd_snd_snd
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.2 =
      topologicalCurrentSugawaraReadout
        (𝕜 := 𝕜)
        (V := VirasoroProject.ChargedFockSpace 𝕜 p.1)
        (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) p.1 p.2.1 p.2.2).heisenberg.currentRep := by
  rfl

/-- The combined readout is continuous on the discrete parameter space. -/
theorem continuous_boundaryAtlasCyclotomicSugawaraReadout :
    Continuous (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)) := by
  simpa [boundaryAtlasCyclotomicSugawaraReadout] using
    (continuous_of_discreteTopology :
      Continuous (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)))

/-- The combined readout is locally constant on the discrete parameter space. -/
theorem isLocallyConstant_boundaryAtlasCyclotomicSugawaraReadout :
    IsLocallyConstant (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)) := by
  simpa [boundaryAtlasCyclotomicSugawaraReadout] using
    (IsLocallyConstant.of_discrete
      (f := boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)))

/-- The Sugawara central generator readout is preserved in the combined packet. -/
theorem boundaryAtlasCyclotomicSugawaraReadout_currentSugawara_central
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.2
        (VirasoroAlgebra.cgen 𝕜) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 p.1 →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 p.1) := by
  simpa [boundaryAtlasCyclotomicSugawaraReadout] using
    (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_central
      (𝕜 := 𝕜) p.1)

/-- The `lgen` readout is preserved in the combined packet. -/
theorem boundaryAtlasCyclotomicSugawaraReadout_currentSugawara_lgen_apply
    (p : 𝕜 × SixthRootParameter) (n : Int) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.2
        (VirasoroAlgebra.lgen 𝕜 n) =
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.sugawaraStressMode
        ((InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) p.1 p.2.1 p.2.2).heisenberg.currentRep)
        n := by
  simpa [boundaryAtlasCyclotomicSugawaraReadout] using
    (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_lgen_apply
      (𝕜 := 𝕜) p.1 n)
