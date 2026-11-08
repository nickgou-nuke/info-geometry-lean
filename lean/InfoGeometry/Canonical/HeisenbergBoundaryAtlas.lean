/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Heisenberg Boundary Atlas

This module pairs the two canonical boundary surfaces of the Heisenberg corridor
without introducing a wrapper `structure`:
1. The finite-mode `ModuleCat 𝕜` colimit readout of `HeisenbergAlgebra 𝕜`.
2. The current/Sugawara boundary representation on `ChargedFockSpace 𝕜 α`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge`:
    `heisenbergFiniteMode_boundaryReadout`.
  * `InfoGeometry.Canonical.CurrentSugawaraBridge`:
    `chargedFockSpaceCurrentHeisenbergRep`, `CurrentHeisenbergRep.currentSugawaraRepresentation`,
    `CurrentHeisenbergRep.currentSugawaraRepresentation_central`,
    `CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply`.
- BUCKET 2 (Deconfabulation):
  * Replaced the `Atlas` wrapper `structure` and `:= rfl` projection lemmas with an
    explicit Cartesian product type `Atlas` and explicit projection functions
    `Atlas.finiteModeMap` and `Atlas.currentRep`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `Atlas`, `Atlas.finiteModeMap`, `Atlas.currentRep`, `canonicalAtlas`.
  * `canonicalAtlas_finiteMode_boundaryReadout`: stage-wise exhaustion of
    `HeisenbergAlgebra 𝕜` through `(canonicalAtlas α).finiteModeMap`.
  * `canonicalAtlas_currentSugawara_central`: central charge $c = 1$ action on
    `ChargedFockSpace 𝕜 α`.
  * `canonicalAtlas_currentSugawara_lgen_apply`: Sugawara stress-mode realization of
    $L_n$ on `ChargedFockSpace 𝕜 α`.
  * `canonicalAtlas_currentSugawara_lgen_central_commutator`: every Sugawara Virasoro
    generator $L_n$ commutes with the central element $C$ on `ChargedFockSpace 𝕜 α`.
-/

namespace InfoGeometry.Canonical.HeisenbergBoundaryAtlas

open CategoryTheory
open CategoryTheory.Limits
open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraBridge

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Canonical atlas carrier for the Heisenberg boundary corridor: the Cartesian product
of the finite-mode colimit morphism and the current Heisenberg representation on the
charged Fock space. -/
def Atlas (α : 𝕜) : Type _ :=
  (heisenbergFiniteModeColimit (𝕜 := 𝕜) ⟶
    ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜)) ×
  CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)

/-- The finite-mode colimit map projection from a Heisenberg boundary atlas pair. -/
def Atlas.finiteModeMap {α : 𝕜} (A : Atlas (𝕜 := 𝕜) α) :
    heisenbergFiniteModeColimit (𝕜 := 𝕜) ⟶
      ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜) :=
  A.1

/-- The current Heisenberg representation projection from a Heisenberg boundary atlas pair. -/
def Atlas.currentRep {α : 𝕜} (A : Atlas (𝕜 := 𝕜) α) :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  A.2

/-- The canonical atlas pair combining `heisenbergFiniteModeColimitMap` and
`chargedFockSpaceCurrentHeisenbergRep`. -/
noncomputable def canonicalAtlas (α : 𝕜) : Atlas (𝕜 := 𝕜) α :=
  (heisenbergFiniteModeColimitMap (𝕜 := 𝕜),
   chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/-- Every element of `HeisenbergAlgebra 𝕜` is recovered from a finite stage via the
`finiteModeMap` component of `canonicalAtlas`. -/
theorem canonicalAtlas_finiteMode_boundaryReadout
    (α : 𝕜) (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (canonicalAtlas (𝕜 := 𝕜) α).finiteModeMap.hom
            ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
  rcases HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout
      (𝕜 := 𝕜) X with ⟨s, x, hx⟩
  refine ⟨s, x, ?_⟩
  unfold canonicalAtlas Atlas.finiteModeMap
  exact hx

/-- The Sugawara central generator `cgen 𝕜` acts as the identity operator on
`ChargedFockSpace 𝕜 α` via the `currentRep` component of `canonicalAtlas`. -/
theorem canonicalAtlas_currentSugawara_central
    (α : 𝕜) :
    (canonicalAtlas (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.cgen 𝕜) =
      (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) := by
  unfold canonicalAtlas Atlas.currentRep
  exact CurrentHeisenbergRep.currentSugawaraRepresentation_central
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/-- Each Virasoro mode `lgen 𝕜 n` acts as the Sugawara normal-ordered stress mode
`sugawaraStressMode n` on `ChargedFockSpace 𝕜 α`. -/
theorem canonicalAtlas_currentSugawara_lgen_apply
    (α : 𝕜) (n : Int) :
    (canonicalAtlas (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 n) =
      (canonicalAtlas (𝕜 := 𝕜) α).currentRep.sugawaraStressMode n := by
  unfold canonicalAtlas Atlas.currentRep
  exact CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) n

/-- Every Sugawara Virasoro generator `lgen 𝕜 n` commutes with the central element
`cgen 𝕜` in the endomorphism algebra of `ChargedFockSpace 𝕜 α`. -/
theorem canonicalAtlas_currentSugawara_lgen_central_commutator
    (α : 𝕜) (n : Int) :
    ((canonicalAtlas (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((canonicalAtlas (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.cgen 𝕜)) = 0 := by
  rw [canonicalAtlas_currentSugawara_lgen_apply, canonicalAtlas_currentSugawara_central]
  ext v
  simp [LinearMap.commutator]

end InfoGeometry.Canonical.HeisenbergBoundaryAtlas
