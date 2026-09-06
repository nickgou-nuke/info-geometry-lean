import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological

/-!
# Compatibility bridge between the Heisenberg boundary atlas and the
finite-mode direct-limit topology

This file does not identify the Heisenberg corridor with any symbolic-latent
boundary completion.  It records the honest theorem that the boundary atlas
packet exposes the same finite-mode readout already packaged by the
direct-limit topological owner.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasDirectLimitTopologicalBridge

open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological
open InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge
open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The finite-mode field of the Heisenberg boundary atlas packet is exactly
the topological direct-limit readout. -/
theorem boundaryAtlas_finiteModeMap_eq_colimitMap
    (α : 𝕜) :
    (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α).2.finiteModeMap.hom =
      (InfoGeometry.Canonical.heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  rfl

/-- The Heisenberg boundary atlas packet still determines the same exhaustive
finite-mode readout at the stage level. -/
theorem boundaryAtlas_finiteModeReadout_stage_eq
    (α : 𝕜) (X : VirasoroProject.HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : InfoGeometry.Canonical.heisenbergFiniteModeStage (𝕜 := 𝕜) s,
      (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜))
            ((colimit.ι (InfoGeometry.Canonical.heisenbergFiniteModeDiagram (𝕜 := 𝕜))
                s).hom x) = X := by
  simpa [topologicalHeisenbergBoundaryAtlas, topologicalHeisenbergFiniteModeDirectLimitMap,
    heisenbergFiniteModeDirectLimitMap_eq] using
    heisenbergFiniteModeDirectLimit_boundaryReadout (𝕜 := 𝕜) X

end InfoGeometry.Topology.HeisenbergBoundaryAtlasDirectLimitTopologicalBridge
