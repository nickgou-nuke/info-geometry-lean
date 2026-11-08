/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological

/-!
# Topological Bridge from the Heisenberg Boundary Atlas to the Sugawara Readout

This module constructs the discrete topological bundle `boundaryAtlasSugawaraBundle`
pairing the Heisenberg boundary atlas with its current-algebra Sugawara Virasoro
representation, and proves its projection, continuity, local constancy, central
generator, and stress-mode identities.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergBoundaryAtlas`: `Atlas`, `canonicalAtlas`,
    `canonicalAtlas_currentSugawara_central`, `canonicalAtlas_currentSugawara_lgen_apply`.
  * `InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological`:
    `topologicalCurrentSugawaraReadout`.
- BUCKET 2 (Deconfabulation):
  * All projection and Sugawara evaluation identities are proved via explicit unfolding
    and reduction to the canonical boundary-atlas theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `boundaryAtlasSugawaraBundle`: dependent section pairing `canonicalAtlas α` with its
    Sugawara Virasoro Lie homomorphism.
  * `boundaryAtlasSugawaraBundle_fst`, `boundaryAtlasSugawaraBundle_snd_fst`,
    `boundaryAtlasSugawaraBundle_snd_snd`: coordinate projections.
  * `continuous_boundaryAtlasSugawaraBundle`,
    `isLocallyConstant_boundaryAtlasSugawaraBundle`: continuity and local constancy.
  * `boundaryAtlasSugawaraBundle_currentSugawara_central`,
    `boundaryAtlasSugawaraBundle_currentSugawara_lgen_apply`: Sugawara central and
    stress-mode evaluations.
-/

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasCurrentSugawaraTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

local instance boundaryAtlasEndLieRing (α : 𝕜) :
    LieRing
      (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
        VirasoroProject.ChargedFockSpace 𝕜 α) :=
  LieRing.ofAssociativeRing

instance boundaryAtlasSugawaraBundleTopologicalSpace :
    TopologicalSpace
      (Σ α : 𝕜,
        InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
          (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
            (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))) := ⊥

instance boundaryAtlasSugawaraBundleDiscreteTopology :
    DiscreteTopology
      (Σ α : 𝕜,
        InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
          (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
            (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α))) := DiscreteTopology.mk (Eq.refl _)

/-- The Heisenberg boundary atlas together with its Sugawara Virasoro readout. -/
def boundaryAtlasSugawaraBundle (α : 𝕜) :
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

/-- Base charge coordinate of `boundaryAtlasSugawaraBundle α`. -/
@[simp] theorem boundaryAtlasSugawaraBundle_fst (α : 𝕜) :
    (boundaryAtlasSugawaraBundle (𝕜 := 𝕜) α).1 = α := by
  unfold boundaryAtlasSugawaraBundle
  exact Eq.refl _

/-- First fiber component of `boundaryAtlasSugawaraBundle α` recovers `canonicalAtlas α`. -/
@[simp] theorem boundaryAtlasSugawaraBundle_snd_fst (α : 𝕜) :
    (boundaryAtlasSugawaraBundle (𝕜 := 𝕜) α).2.1 =
      InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α := by
  unfold boundaryAtlasSugawaraBundle
  exact Eq.refl _

/-- Second fiber component of `boundaryAtlasSugawaraBundle α` recovers the Sugawara readout. -/
@[simp] theorem boundaryAtlasSugawaraBundle_snd_snd (α : 𝕜) :
    (boundaryAtlasSugawaraBundle (𝕜 := 𝕜) α).2.2 =
      topologicalCurrentSugawaraReadout
        (𝕜 := 𝕜)
        (V := VirasoroProject.ChargedFockSpace 𝕜 α)
        (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α).currentRep := by
  unfold boundaryAtlasSugawaraBundle
  exact Eq.refl _

/-- The boundary atlas current/Sugawara bridge is continuous on the discrete parameter space. -/
theorem continuous_boundaryAtlasSugawaraBundle :
    Continuous (boundaryAtlasSugawaraBundle (𝕜 := 𝕜)) := by
  unfold boundaryAtlasSugawaraBundle
  exact continuous_of_discreteTopology

/-- The boundary atlas current/Sugawara bridge is locally constant on the discrete parameter space. -/
theorem isLocallyConstant_boundaryAtlasSugawaraBundle :
    IsLocallyConstant (boundaryAtlasSugawaraBundle (𝕜 := 𝕜)) := by
  unfold boundaryAtlasSugawaraBundle
  exact IsLocallyConstant.of_discrete

/-- The Sugawara central generator readout is preserved in `boundaryAtlasSugawaraBundle`. -/
theorem boundaryAtlasSugawaraBundle_currentSugawara_central
    (α : 𝕜) :
    (boundaryAtlasSugawaraBundle (𝕜 := 𝕜) α).2.2
        (VirasoroAlgebra.cgen 𝕜) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
  change (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas
    (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
      (VirasoroAlgebra.cgen 𝕜) = _
  exact InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_central
    (𝕜 := 𝕜) α

/-- The Virasoro stress generator `lgen n` readout is preserved in `boundaryAtlasSugawaraBundle`. -/
theorem boundaryAtlasSugawaraBundle_currentSugawara_lgen_apply
    (α : 𝕜) (n : Int) :
    (boundaryAtlasSugawaraBundle (𝕜 := 𝕜) α).2.2
        (VirasoroAlgebra.lgen 𝕜 n) =
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.sugawaraStressMode
        ((InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α).currentRep)
        n := by
  change (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas
    (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
      (VirasoroAlgebra.lgen 𝕜 n) = _
  exact InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_lgen_apply
    (𝕜 := 𝕜) α n

end
end InfoGeometry.Topology.HeisenbergBoundaryAtlasCurrentSugawaraTopological
