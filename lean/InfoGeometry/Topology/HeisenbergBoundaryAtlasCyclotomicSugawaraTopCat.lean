/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat Packaging for the Heisenberg Boundary / Sixth-Root / Sugawara Bundle

This module realizes `BoundaryAtlasCyclotomicSugawaraBundle` and its parameter base
`𝕜 × SixthRootParameter` as objects in `TopCat`, constructs the projection and canonical
section morphisms, and proves the retraction law `atlasSection ≫ projection = 𝟙 _`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological`:
    `BoundaryAtlasCyclotomicSugawaraBundle`, `boundaryAtlasCyclotomicSugawaraReadout`,
    `continuous_boundaryAtlasCyclotomicSugawaraReadout`.
- BUCKET 2 (Deconfabulation):
  * Categorical retraction is proved via `TopCat.hom_ext` and explicit product extensionality.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `topCat`, `parameterTopCat`, `projection`, `atlasSection`.
  * `atlasSection_projection`: categorical retraction `atlasSection ≫ projection = 𝟙 _`.
  * `atlasSection_projection_apply`: pointwise evaluation at `p : 𝕜 × SixthRootParameter`.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopCat

open CategoryTheory
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The combined Heisenberg boundary / sixth-root / Sugawara bundle as a `TopCat` object. -/
abbrev topCat : TopCat :=
  TopCat.of (BoundaryAtlasCyclotomicSugawaraBundle (𝕜 := 𝕜))

/-- The parameter space `𝕜 × SixthRootParameter` as a `TopCat` object. -/
abbrev parameterTopCat : TopCat :=
  TopCat.of (𝕜 × SixthRootParameter)

/-- Projection morphism from the combined bundle back to its input parameter pair. -/
noncomputable def projection :
    topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) :=
  TopCat.ofHom ⟨fun p => (p.1, p.2.1), continuous_of_discreteTopology⟩

/-- Canonical section morphism from parameters into the combined bundle. -/
noncomputable def atlasSection :
    parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) :=
  TopCat.ofHom ⟨boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜),
    continuous_boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)⟩

/-- Categorical retraction law `atlasSection ≫ projection = 𝟙 _` in `TopCat`. -/
@[simp] theorem atlasSection_projection :
    atlasSection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext p
  · unfold atlasSection projection boundaryAtlasCyclotomicSugawaraReadout
    exact Eq.refl _
  · unfold atlasSection projection boundaryAtlasCyclotomicSugawaraReadout
    exact Eq.refl _

/-- Pointwise evaluation of `atlasSection ≫ projection` at `p : 𝕜 × SixthRootParameter`. -/
@[simp] theorem atlasSection_projection_apply (p : 𝕜 × SixthRootParameter) :
    (atlasSection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)) p = p := by
  rw [atlasSection_projection (𝕜 := 𝕜)]
  exact Eq.refl _

end InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopCat
