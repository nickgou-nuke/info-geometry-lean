/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
import InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological

/-!
# Topological Bridge for the Heisenberg Boundary Atlas, Sixth-Root Lane, and Current Sugawara Readout

This module constructs the discrete topological bundle `BoundaryAtlasCyclotomicSugawaraBundle`
combining the Heisenberg boundary atlas, the sixth-root cyclotomic parameter, and the
Sugawara Virasoro representation on `ChargedFockSpace 𝕜 α`, together with coordinate
projections, continuity, local constancy, and Sugawara central/stress-mode evaluations.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergCyclotomicAtlas`: `Atlas`, `canonicalAtlas`,
    `canonicalAtlas_currentSugawara_central`.
  * `InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological`: `SixthRootParameter`.
  * `InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological`:
    `topologicalCurrentSugawaraReadout`.
- BUCKET 2 (Deconfabulation):
  * All coordinate projections and Sugawara generator evaluations are proved via
    explicit definitional unfolding and reduction to the canonical boundary-atlas theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `BoundaryAtlasCyclotomicSugawaraBundle`: total-space bundle over `𝕜`.
  * `boundaryAtlasCyclotomicSugawaraReadout`: section from `𝕜 × SixthRootParameter`.
  * `boundaryAtlasCyclotomicSugawaraReadout_fst`,
    `boundaryAtlasCyclotomicSugawaraReadout_snd_fst`,
    `boundaryAtlasCyclotomicSugawaraReadout_snd_snd_fst`,
    `boundaryAtlasCyclotomicSugawaraReadout_snd_snd_snd`: coordinate projections.
  * `continuous_boundaryAtlasCyclotomicSugawaraReadout`,
    `isLocallyConstant_boundaryAtlasCyclotomicSugawaraReadout`: continuity and local constancy.
  * `boundaryAtlasCyclotomicSugawaraReadout_currentSugawara_central`,
    `boundaryAtlasCyclotomicSugawaraReadout_currentSugawara_lgen_apply`: Sugawara generator
    identities.
-/

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological
open VirasoroProject

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergCyclotomicParameterTopologicalSpace :
    TopologicalSpace 𝕜 := ⊥

instance heisenbergCyclotomicParameterDiscreteTopology :
    DiscreteTopology 𝕜 := DiscreteTopology.mk (Eq.refl _)

instance heisenbergCyclotomicSugawaraInputTopologicalSpace :
    TopologicalSpace (𝕜 × SixthRootParameter) := ⊥

instance heisenbergCyclotomicSugawaraInputDiscreteTopology :
    DiscreteTopology (𝕜 × SixthRootParameter) := DiscreteTopology.mk (Eq.refl _)

/-- Total-space bundle combining the charge parameter, sixth-root parameter,
cyclotomic atlas, and Sugawara Virasoro Lie homomorphism. -/
abbrev BoundaryAtlasCyclotomicSugawaraBundle :=
  Σ α : 𝕜,
    SixthRootParameter ×
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.Atlas (𝕜 := 𝕜) α ×
        (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆
          (VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)))

instance boundaryAtlasCyclotomicSugawaraBundleTopologicalSpace :
    TopologicalSpace (BoundaryAtlasCyclotomicSugawaraBundle (𝕜 := 𝕜)) := ⊥

instance boundaryAtlasCyclotomicSugawaraBundleDiscreteTopology :
    DiscreteTopology (BoundaryAtlasCyclotomicSugawaraBundle (𝕜 := 𝕜)) := DiscreteTopology.mk (Eq.refl _)

/-- The combined Heisenberg boundary / sixth-root / Sugawara readout. -/
def boundaryAtlasCyclotomicSugawaraReadout
    (p : 𝕜 × SixthRootParameter) :
    BoundaryAtlasCyclotomicSugawaraBundle (𝕜 := 𝕜) :=
  ⟨p.1,
    (p.2,
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
        (𝕜 := 𝕜) p.1 p.2.1 p.2.2,
        topologicalCurrentSugawaraReadout
          (𝕜 := 𝕜)
          (V := VirasoroProject.ChargedFockSpace 𝕜 p.1)
          (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
            (𝕜 := 𝕜) p.1 p.2.1 p.2.2).heisenberg.currentRep))⟩

/-- First coordinate of `boundaryAtlasCyclotomicSugawaraReadout p` is the charge parameter `p.1`. -/
@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_fst
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).1 = p.1 := by
  unfold boundaryAtlasCyclotomicSugawaraReadout
  exact Eq.refl _

/-- Sixth-root parameter component of `boundaryAtlasCyclotomicSugawaraReadout p`. -/
@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_snd_fst
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.1 = p.2 := by
  unfold boundaryAtlasCyclotomicSugawaraReadout
  exact Eq.refl _

/-- Cyclotomic atlas component of `boundaryAtlasCyclotomicSugawaraReadout p`. -/
@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_snd_snd_fst
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.1 =
      (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
        (𝕜 := 𝕜) p.1 p.2.1 p.2.2) := by
  unfold boundaryAtlasCyclotomicSugawaraReadout
  exact Eq.refl _

/-- Sugawara Virasoro Lie homomorphism component of `boundaryAtlasCyclotomicSugawaraReadout p`. -/
@[simp] theorem boundaryAtlasCyclotomicSugawaraReadout_snd_snd_snd
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.2 =
      topologicalCurrentSugawaraReadout
        (𝕜 := 𝕜)
        (V := VirasoroProject.ChargedFockSpace 𝕜 p.1)
        (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) p.1 p.2.1 p.2.2).heisenberg.currentRep := by
  unfold boundaryAtlasCyclotomicSugawaraReadout
  exact Eq.refl _

/-- The combined readout is continuous on the discrete parameter space. -/
theorem continuous_boundaryAtlasCyclotomicSugawaraReadout :
    Continuous (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)) := by
  unfold boundaryAtlasCyclotomicSugawaraReadout
  exact continuous_of_discreteTopology

/-- The combined readout is locally constant on the discrete parameter space. -/
theorem isLocallyConstant_boundaryAtlasCyclotomicSugawaraReadout :
    IsLocallyConstant (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)) := by
  unfold boundaryAtlasCyclotomicSugawaraReadout
  exact IsLocallyConstant.of_discrete

/-- The Sugawara central generator readout is preserved in the combined bundle. -/
theorem boundaryAtlasCyclotomicSugawaraReadout_currentSugawara_central
    (p : 𝕜 × SixthRootParameter) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.2
        (VirasoroAlgebra.cgen 𝕜) =
      (1 :
        VirasoroProject.ChargedFockSpace 𝕜 p.1 →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 p.1) := by
  change (InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
      (𝕜 := 𝕜) p.1 p.2.1 p.2.2).heisenberg.currentRep.currentSugawaraRepresentation
      (VirasoroAlgebra.cgen 𝕜) =
        (1 : VirasoroProject.ChargedFockSpace 𝕜 p.1 →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 p.1)
  exact InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_currentSugawara_central
    (𝕜 := 𝕜) p.1 p.2.1 p.2.2

/-- The Virasoro stress generator `lgen n` readout is preserved in the combined bundle. -/
theorem boundaryAtlasCyclotomicSugawaraReadout_currentSugawara_lgen_apply
    (p : 𝕜 × SixthRootParameter) (n : Int) :
    (boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜) p).2.2.2
        (VirasoroAlgebra.lgen 𝕜 n) =
      InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep.sugawaraStressMode
        ((InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas
          (𝕜 := 𝕜) p.1 p.2.1 p.2.2).heisenberg.currentRep)
        n := by
  change (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas
      (𝕜 := 𝕜) p.1).currentRep.currentSugawaraRepresentation
      (VirasoroAlgebra.lgen 𝕜 n) =
        (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas
          (𝕜 := 𝕜) p.1).currentRep.sugawaraStressMode n
  exact InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_lgen_apply
    (𝕜 := 𝕜) p.1 n

end
end InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological
