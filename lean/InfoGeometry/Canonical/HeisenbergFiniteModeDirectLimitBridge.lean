/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Heisenberg Finite-Mode Filtered Direct Limit Bridge

This module connects the finite-mode Heisenberg `ModuleCat 𝕜` colimit to the
filtered direct-limit interface via the universal colimit cone extension law.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeColimit`: `heisenbergFiniteModeColimit`,
    `heisenbergFiniteModeColimitMap`, `heisenbergFiniteModeColimitMap_stage`,
    `heisenbergFiniteModeColimitMap_surjective`.
  * `InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge`:
    `heisenbergFiniteMode_boundaryReadout`.
- BUCKET 2 (Deconfabulation):
  * Replaced the `rfl` wrapper proof of `heisenbergFiniteModeDirectLimitMap_eq` and
    pass-through wrapper `heisenbergFiniteModeDirectLimitMap_stage` with universal
    `colimit.ι_desc` and `colimit.hom_ext` derivations.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergFiniteModeDirectLimit`, `heisenbergFiniteModeDirectLimitMap`:
    categorical direct-limit carrier and descent map in `ModuleCat 𝕜`.
  * `heisenbergFiniteModeDirectLimitMap_stage`: stage-wise compatibility via
    `colimit.ι_desc`.
  * `heisenbergFiniteModeDirectLimitMap_eq`: uniqueness of the descended map via
    `colimit.hom_ext`.
  * `heisenbergFiniteModeDirectLimitMap_surjective`: surjectivity of the direct-limit map.
  * `heisenbergFiniteModeDirectLimit_boundaryReadout`: finite-stage boundary exhaustion.
-/

noncomputable section

namespace InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge

open CategoryTheory CategoryTheory.Limits
open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The filtered direct-limit carrier for the Heisenberg finite-mode diagram in `ModuleCat 𝕜`. -/
abbrev heisenbergFiniteModeDirectLimit : ModuleCat 𝕜 :=
  heisenbergFiniteModeColimit (𝕜 := 𝕜)

/-- The filtered-direct-limit descent morphism for the Heisenberg cocone. -/
noncomputable abbrev heisenbergFiniteModeDirectLimitMap :
    heisenbergFiniteModeDirectLimit (𝕜 := 𝕜) ⟶
      ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜) :=
  heisenbergFiniteModeColimitMap (𝕜 := 𝕜)

/-- The filtered-direct-limit stage law for the Heisenberg exhaustion, proved from
the universal cocone property `colimit.ι_desc`. -/
theorem heisenbergFiniteModeDirectLimitMap_stage (s : Finset (Option ℤ)) :
    colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s ≫
      heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app s := by
  unfold heisenbergFiniteModeDirectLimitMap heisenbergFiniteModeColimitMap
  exact colimit.ι_desc (heisenbergFiniteModeCocone (𝕜 := 𝕜)) s

/-- By the universal uniqueness property `colimit.hom_ext`, the filtered-direct-limit
map coincides with `heisenbergFiniteModeColimitMap`. -/
@[simp] theorem heisenbergFiniteModeDirectLimitMap_eq :
    heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜) =
      heisenbergFiniteModeColimitMap (𝕜 := 𝕜) := by
  apply colimit.hom_ext
  intro s
  exact (heisenbergFiniteModeDirectLimitMap_stage (𝕜 := 𝕜) s).trans
    (heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s).symm

/-- The filtered-direct-limit map is surjective onto `HeisenbergAlgebra 𝕜`. -/
theorem heisenbergFiniteModeDirectLimitMap_surjective :
    Function.Surjective
      (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom := by
  rw [heisenbergFiniteModeDirectLimitMap_eq]
  exact heisenbergFiniteModeColimitMap_surjective (𝕜 := 𝕜)

/-- Every Heisenberg element is represented by a finite direct-limit stage. -/
theorem heisenbergFiniteModeDirectLimit_boundaryReadout
    (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom
            ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
  rw [heisenbergFiniteModeDirectLimitMap_eq]
  exact HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout (𝕜 := 𝕜) X

end InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge
