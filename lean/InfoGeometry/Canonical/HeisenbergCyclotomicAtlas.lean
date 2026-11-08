/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HeisenbergBoundaryAtlas
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSixthRootCubicChargeBridge

/-!
# Heisenberg Cyclotomic Atlas

This module pairs the Heisenberg finite-mode boundary atlas with a sixth-root
cyclotomic parameter $\{p \in \mathbb{C}^\times \mid p^6 = 1\}$ without introducing a
wrapper `structure`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergBoundaryAtlas`: `Atlas`, `canonicalAtlas`,
    `canonicalAtlas_finiteMode_boundaryReadout`, `canonicalAtlas_currentSugawara_central`.
  * `InfoGeometry.Canonical.ZornSixthRootCubicChargeBridge`:
    `zornSixthRoot_effectiveCubeRoot`, `cubicProjectors_sum_of_sixthRoot`.
- BUCKET 2 (Deconfabulation):
  * Replaced the `Atlas` wrapper `structure`, embedded `sixthRoot_pow` `Prop` field,
    `:= rfl` projection lemmas, and unused-binder theorem with an explicit Cartesian
    product type `Atlas (α : 𝕜)` and explicit projection functions.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `Atlas`, `Atlas.heisenberg`, `Atlas.sixthRoot`, `Atlas.sixthRoot_pow`, `canonicalAtlas`.
  * `canonicalAtlas_heisenbergFiniteMode_boundaryReadout`: finite-stage colimit exhaustion
    through `(canonicalAtlas α p hp).heisenberg.finiteModeMap`.
  * `canonicalAtlas_currentSugawara_central`: Sugawara central charge $c = 1$ identity on
    `ChargedFockSpace 𝕜 α`.
  * `canonicalAtlas_effectiveCubeRoot`: the squared sixth-root parameter of
    `canonicalAtlas α p hp` is a primitive-compatible cube root of unity $((p^2)^3 = 1)$.
  * `canonicalAtlas_sixthRoot_and_central_readout`: joint certificate of the effective
    cube-root law and Sugawara central identity on `canonicalAtlas α p hp`.
-/

namespace InfoGeometry.Canonical.HeisenbergCyclotomicAtlas

open CategoryTheory
open CategoryTheory.Limits
open VirasoroProject
open ZornMatrix

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Combined boundary carrier for the verified Heisenberg boundary atlas and a sixth root
of unity $\{p \in \mathbb{C}^\times \mid (p : \mathbb{C})^6 = 1\}$. -/
def Atlas (α : 𝕜) : Type _ :=
  InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
    {p : ℂˣ // (p : ℂ) ^ 6 = 1}

/-- The Heisenberg finite-mode boundary atlas projection. -/
def Atlas.heisenberg {α : 𝕜} (A : Atlas (𝕜 := 𝕜) α) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α :=
  A.1

/-- The sixth-root Zorn scaling unit projection. -/
def Atlas.sixthRoot {α : 𝕜} (A : Atlas (𝕜 := 𝕜) α) : ℂˣ :=
  A.2.1

/-- The sixth-root power identity $((A.\mathrm{sixthRoot} : \mathbb{C})^6 = 1)$ carried
by the subtype second factor of `Atlas`. -/
theorem Atlas.sixthRoot_pow {α : 𝕜} (A : Atlas (𝕜 := 𝕜) α) :
    (A.sixthRoot : ℂ) ^ 6 = 1 := by
  unfold Atlas.sixthRoot
  exact A.2.2

/-- The combined atlas built from the canonical Heisenberg boundary atlas and a sixth
root of unity. -/
noncomputable def canonicalAtlas (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    Atlas (𝕜 := 𝕜) α :=
  (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α,
   ⟨p, hp⟩)

/-- The Heisenberg finite-mode boundary readout is available inside the combined atlas. -/
theorem canonicalAtlas_heisenbergFiniteMode_boundaryReadout
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (canonicalAtlas (𝕜 := 𝕜) α p hp).heisenberg.finiteModeMap.hom
            ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
  rcases HeisenbergBoundaryAtlas.canonicalAtlas_finiteMode_boundaryReadout
      (𝕜 := 𝕜) α X with ⟨s, x, hx⟩
  refine ⟨s, x, ?_⟩
  unfold canonicalAtlas Atlas.heisenberg
  exact hx

/-- The Sugawara current boundary central readout is preserved in the combined atlas. -/
theorem canonicalAtlas_currentSugawara_central
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (canonicalAtlas (𝕜 := 𝕜) α p hp).heisenberg.currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.cgen 𝕜) =
      (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) := by
  unfold canonicalAtlas Atlas.heisenberg
  exact HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_central (𝕜 := 𝕜) α

/-- The sixth-root parameter of `canonicalAtlas α p hp` induces the effective cube-root
action $(((canonicalAtlas\;\alpha\;p\;hp).\mathrm{sixthRoot})^2)^3 = 1$. -/
theorem canonicalAtlas_effectiveCubeRoot
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (((canonicalAtlas (𝕜 := 𝕜) α p hp).sixthRoot : ℂ) ^ 2) ^ 3 = 1 := by
  unfold canonicalAtlas Atlas.sixthRoot
  exact zornSixthRoot_effectiveCubeRoot p hp

/-- Joint synthesis of the effective cube-root law and Sugawara central charge identity
for `canonicalAtlas α p hp`. -/
theorem canonicalAtlas_sixthRoot_and_central_readout
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (((canonicalAtlas (𝕜 := 𝕜) α p hp).sixthRoot : ℂ) ^ 2) ^ 3 = 1 ∧
    (canonicalAtlas (𝕜 := 𝕜) α p hp).heisenberg.currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.cgen 𝕜) =
      (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) := by
  constructor
  · exact canonicalAtlas_effectiveCubeRoot (𝕜 := 𝕜) α p hp
  · exact canonicalAtlas_currentSugawara_central (𝕜 := 𝕜) α p hp

end InfoGeometry.Canonical.HeisenbergCyclotomicAtlas
