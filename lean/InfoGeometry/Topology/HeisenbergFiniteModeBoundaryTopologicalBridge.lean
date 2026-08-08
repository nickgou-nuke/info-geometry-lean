import Mathlib
import InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit

/-!
# Topological readout for the finite-mode Heisenberg boundary bridge

This file packages the already-proved finite-mode Heisenberg boundary
exhaustion as a topological packet.  The source and target are given discrete
topologies, so continuity and local constancy are bookkeeping consequences of
the canonical boundary property.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeBoundaryTopologicalBridge

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical
open InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergAlgebraTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergAlgebraDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := ⟨rfl⟩

/-- A finite-mode Heisenberg boundary property packaged as a topological packet. -/
structure HeisenbergFiniteModeBoundaryPacket where
  current : HeisenbergAlgebra 𝕜
  stage : Finset (Option ℤ)
  property : InfoGeometry.Canonical.heisenbergFiniteModeStage (𝕜 := 𝕜) stage
  boundaryEq :
    (InfoGeometry.Canonical.heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        ((colimit.ι (InfoGeometry.Canonical.heisenbergFiniteModeDiagram (𝕜 := 𝕜)) stage).hom property) =
      current

instance heisenbergFiniteModeBoundaryPacketTopologicalSpace :
    TopologicalSpace (HeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeBoundaryPacketDiscreteTopology :
    DiscreteTopology (HeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜)) := ⟨rfl⟩

/-- The canonical boundary packet selected from the finite-mode exhaustion. -/
noncomputable def topologicalHeisenbergFiniteModeBoundaryPacket
    (X : HeisenbergAlgebra 𝕜) :
    HeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜) := by
  classical
  let s : Finset (Option ℤ) :=
    Classical.choose
      (InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout
        (𝕜 := 𝕜) X)
  have hxStage :
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
          ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
    simpa [s] using
      (Classical.choose_spec
        (InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout
          (𝕜 := 𝕜) X))
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    Classical.choose hxStage
  have hx :
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X :=
    Classical.choose_spec hxStage
  exact ⟨X, s, x, hx⟩

/-- The canonical boundary packet is continuous on the discrete Heisenberg carrier. -/
theorem continuous_topologicalHeisenbergFiniteModeBoundaryPacket :
    Continuous (topologicalHeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeBoundaryPacket] using
    (continuous_of_discreteTopology :
      Continuous (topologicalHeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜)))

/-- The canonical boundary packet is locally constant on the discrete Heisenberg carrier. -/
theorem isLocallyConstant_topologicalHeisenbergFiniteModeBoundaryPacket :
    IsLocallyConstant (topologicalHeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜)) := by
  simpa [topologicalHeisenbergFiniteModeBoundaryPacket] using
    (IsLocallyConstant.of_discrete
      (f := topologicalHeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜)))

/-- The boundary packet viewed as a `TopCat` object. -/
abbrev topCat : TopCat :=
  TopCat.of (HeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜))

/-- The Heisenberg carrier viewed as a `TopCat` object. -/
abbrev parameterTopCat : TopCat :=
  TopCat.of (HeisenbergAlgebra 𝕜)

/-- The canonical projection from the boundary packet to its Heisenberg current. -/
noncomputable def projection : topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun p => p.current, ?_⟩
  exact continuous_of_discreteTopology

/-- The canonical section of the projection, built from the finite-mode boundary readout. -/
noncomputable def boundarySection : parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun X => topologicalHeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜) X, ?_⟩
  simpa using continuous_topologicalHeisenbergFiniteModeBoundaryPacket (𝕜 := 𝕜)

@[simp] theorem section_projection :
    boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext X
  simp [boundarySection, projection, topologicalHeisenbergFiniteModeBoundaryPacket]

@[simp] theorem section_projection_apply (X : HeisenbergAlgebra 𝕜) :
    (boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)) X = X := by
  simpa using (section_projection (𝕜 := 𝕜))

end
end InfoGeometry.Topology.HeisenbergFiniteModeBoundaryTopologicalBridge
