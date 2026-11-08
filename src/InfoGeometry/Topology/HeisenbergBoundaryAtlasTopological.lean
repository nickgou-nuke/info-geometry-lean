/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergBoundaryAtlas

/-!
# Topological Readout for the Heisenberg Boundary Atlas

This module equips the Heisenberg charge parameter space `𝕜` and the dependent
Heisenberg boundary atlas total space `HeisenbergBoundaryAtlasBundle` with discrete
topologies, and proves continuity, local constancy, and fiber projection laws for
`topologicalHeisenbergBoundaryAtlas`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergBoundaryAtlas`: `Atlas`, `canonicalAtlas`.
  * `Mathlib.Topology.Constructions`: discrete topology and locally constant maps.
- BUCKET 2 (Deconfabulation):
  * All projection and topological theorems are proved through explicit definitional
    unfolding and discrete topology continuity lemmas.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `HeisenbergBoundaryAtlasBundle`: dependent total space `Σ α : 𝕜, Atlas α`.
  * `topologicalHeisenbergBoundaryAtlas`: section `α ↦ ⟨α, canonicalAtlas α⟩`.
  * `topologicalHeisenbergBoundaryAtlas_eq`, `topologicalHeisenbergBoundaryAtlas_fst`,
    `topologicalHeisenbergBoundaryAtlas_snd`: explicit section and projection identities.
  * `continuous_topologicalHeisenbergBoundaryAtlas`,
    `isLocallyConstant_topologicalHeisenbergBoundaryAtlas`: continuity and local constancy.
-/

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological

open InfoGeometry.Canonical
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergBoundaryAtlasParameterTopologicalSpace :
    TopologicalSpace 𝕜 := ⊥

instance heisenbergBoundaryAtlasParameterDiscreteTopology :
    DiscreteTopology 𝕜 := DiscreteTopology.mk (Eq.refl _)

/-- Total-space bundle for the parameterized Heisenberg boundary atlas. -/
abbrev HeisenbergBoundaryAtlasBundle :=
  Σ α : 𝕜, InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α

instance heisenbergBoundaryAtlasBundleTopologicalSpace :
    TopologicalSpace (HeisenbergBoundaryAtlasBundle (𝕜 := 𝕜)) := ⊥

instance heisenbergBoundaryAtlasBundleDiscreteTopology :
    DiscreteTopology (HeisenbergBoundaryAtlasBundle (𝕜 := 𝕜)) := DiscreteTopology.mk (Eq.refl _)

/-- The Heisenberg boundary atlas viewed as a section into the total-space bundle. -/
def topologicalHeisenbergBoundaryAtlas :
    𝕜 → HeisenbergBoundaryAtlasBundle (𝕜 := 𝕜) :=
  fun α => ⟨α, InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas
    (𝕜 := 𝕜) α⟩

/-- Explicit evaluation of `topologicalHeisenbergBoundaryAtlas` at charge parameter `α`. -/
@[simp] theorem topologicalHeisenbergBoundaryAtlas_eq
    (α : 𝕜) :
    topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α =
      ⟨α, InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α⟩ := by
  unfold topologicalHeisenbergBoundaryAtlas
  exact Eq.refl _

/-- Base charge coordinate of `topologicalHeisenbergBoundaryAtlas α`. -/
@[simp] theorem topologicalHeisenbergBoundaryAtlas_fst
    (α : 𝕜) :
    (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α).1 = α := by
  unfold topologicalHeisenbergBoundaryAtlas
  exact Eq.refl _

/-- Fiber atlas coordinate of `topologicalHeisenbergBoundaryAtlas α`. -/
@[simp] theorem topologicalHeisenbergBoundaryAtlas_snd
    (α : 𝕜) :
    (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α).2 =
      InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α := by
  unfold topologicalHeisenbergBoundaryAtlas
  exact Eq.refl _

/-- The Heisenberg boundary atlas readout is continuous on the discrete parameter space. -/
theorem continuous_topologicalHeisenbergBoundaryAtlas :
    Continuous (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergBoundaryAtlas
  exact continuous_of_discreteTopology

/-- The Heisenberg boundary atlas readout is locally constant on the discrete parameter space. -/
theorem isLocallyConstant_topologicalHeisenbergBoundaryAtlas :
    IsLocallyConstant (topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergBoundaryAtlas
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
