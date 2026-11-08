/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Topological Readout for the Current Heisenberg / Sugawara Corridor

This module equips `CurrentHeisenbergRep 𝕜 V` and `VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)`
with discrete topologies and packages `H.currentSugawaraRepresentation` as the
continuous, locally constant map `topologicalCurrentSugawaraReadout`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.CurrentSugawaraBridge`: `CurrentHeisenbergRep`,
    `CurrentHeisenbergRep.currentSugawaraRepresentation`,
    `CurrentHeisenbergRep.currentSugawaraRepresentation_cgen`,
    `CurrentHeisenbergRep.currentSugawaraRepresentation_lgen`.
- BUCKET 2 (Deconfabulation):
  * All evaluation, generator, continuity, and local constancy theorems are proved
    via explicit unfolding.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `topologicalCurrentSugawaraReadout`.
  * `topologicalCurrentSugawaraReadout_eq`,
    `topologicalCurrentSugawaraReadout_cgen`,
    `topologicalCurrentSugawaraReadout_lgen`.
  * `continuous_topologicalCurrentSugawaraReadout`,
    `isLocallyConstant_topologicalCurrentSugawaraReadout`.
-/

namespace InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological

open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

local instance linearEndLieRing (𝕜 V : Type*) [Semiring 𝕜]
    [AddCommGroup V] [Module 𝕜 V] : LieRing (V →ₗ[𝕜] V) :=
  LieRing.ofAssociativeRing

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

instance currentHeisenbergRepTopologicalSpace :
    TopologicalSpace (CurrentHeisenbergRep 𝕜 V) := ⊥

instance currentHeisenbergRepDiscreteTopology :
    DiscreteTopology (CurrentHeisenbergRep 𝕜 V) := DiscreteTopology.mk (Eq.refl _)

instance currentSugawaraMorphismTopologicalSpace :
    TopologicalSpace (VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) := ⊥

instance currentSugawaraMorphismDiscreteTopology :
    DiscreteTopology (VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) := DiscreteTopology.mk (Eq.refl _)

/-- The Sugawara Virasoro Lie homomorphism attached to a `CurrentHeisenbergRep 𝕜 V`. -/
def topologicalCurrentSugawaraReadout (H : CurrentHeisenbergRep 𝕜 V) :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  H.currentSugawaraRepresentation

/-- Explicit identification of `topologicalCurrentSugawaraReadout H` with
`H.currentSugawaraRepresentation`. -/
@[simp] theorem topologicalCurrentSugawaraReadout_eq (H : CurrentHeisenbergRep 𝕜 V) :
    topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V) H =
      H.currentSugawaraRepresentation := by
  unfold topologicalCurrentSugawaraReadout
  exact Eq.refl _

/-- Evaluation of `topologicalCurrentSugawaraReadout H` on the Virasoro central generator `cgen`. -/
@[simp] theorem topologicalCurrentSugawaraReadout_cgen (H : CurrentHeisenbergRep 𝕜 V) :
    topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V) H (VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) := by
  unfold topologicalCurrentSugawaraReadout
  exact H.currentSugawaraRepresentation_cgen

/-- Evaluation of `topologicalCurrentSugawaraReadout H` on the Virasoro stress generator `lgen n`. -/
@[simp] theorem topologicalCurrentSugawaraReadout_lgen
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) :
    topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V) H (VirasoroAlgebra.lgen 𝕜 n) =
      H.sugawaraStressMode n := by
  unfold topologicalCurrentSugawaraReadout
  exact H.currentSugawaraRepresentation_lgen n

/-- The Sugawara readout is continuous for the discrete topology on the source. -/
theorem continuous_topologicalCurrentSugawaraReadout :
    Continuous (topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V)) := by
  unfold topologicalCurrentSugawaraReadout
  exact continuous_of_discreteTopology

/-- The Sugawara readout is locally constant for the discrete topology on the source. -/
theorem isLocallyConstant_topologicalCurrentSugawaraReadout :
    IsLocallyConstant (topologicalCurrentSugawaraReadout (𝕜 := 𝕜) (V := V)) := by
  unfold topologicalCurrentSugawaraReadout
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.CurrentHeisenbergSugawaraTopological
