/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological

/-!
# Compatibility Bridge Between the Heisenberg Boundary Atlas and the Finite-Mode Direct-Limit Topology

This module proves that the finite-mode colimit morphism carried by
`topologicalHeisenbergBoundaryAtlas α` agrees identically with the canonical
finite-mode colimit map and with `topologicalHeisenbergFiniteModeDirectLimitMap`,
and establishes exhaustive finite-stage representability through the topological
direct-limit map.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological`:
    `topologicalHeisenbergBoundaryAtlas`.
  * `InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological`:
    `topologicalHeisenbergFiniteModeDirectLimitMap`.
  * `InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge`:
    `heisenbergFiniteModeDirectLimit_boundaryReadout`.
- BUCKET 2 (Deconfabulation):
  * Both compatibility theorems are proved via explicit unfolding of the boundary atlas
    and direct-limit maps.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `boundaryAtlas_finiteModeMap_eq_colimitMap`: equality of the boundary-atlas finite-mode
    map with `heisenbergFiniteModeColimitMap.hom`.
  * `boundaryAtlas_finiteModeReadout_stage_eq`: every Heisenberg element `X` is represented
    at a finite stage `s` under `topologicalHeisenbergFiniteModeDirectLimitMap`.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasDirectLimitTopologicalBridge

open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open InfoGeometry.Topology.HeisenbergFiniteModeDirectLimitTopological
open InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge
open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type*} [Field 𝕜]

/-- The finite-mode component of `topologicalHeisenbergBoundaryAtlas α` is identically
the canonical finite-mode colimit linear map. -/
theorem boundaryAtlas_finiteModeMap_eq_colimitMap
    (α : 𝕜) :
    (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α).2.finiteModeMap.hom =
      (InfoGeometry.Canonical.heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  unfold topologicalHeisenbergBoundaryAtlas
  rw [InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_finiteModeMap]

/-- Every element `X` of `HeisenbergAlgebra 𝕜` lies in the image of a finite stage `s`
under `topologicalHeisenbergFiniteModeDirectLimitMap`. -/
theorem boundaryAtlas_finiteModeReadout_stage_eq
    (X : VirasoroProject.HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : InfoGeometry.Canonical.heisenbergFiniteModeStage (𝕜 := 𝕜) s,
      (topologicalHeisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜))
            ((colimit.ι (InfoGeometry.Canonical.heisenbergFiniteModeDiagram (𝕜 := 𝕜))
                s).hom x) = X := by
  rcases heisenbergFiniteModeDirectLimit_boundaryReadout (𝕜 := 𝕜) X with ⟨s, x, hx⟩
  refine ⟨s, x, ?_⟩
  unfold topologicalHeisenbergFiniteModeDirectLimitMap
  exact hx

end InfoGeometry.Topology.HeisenbergBoundaryAtlasDirectLimitTopologicalBridge
