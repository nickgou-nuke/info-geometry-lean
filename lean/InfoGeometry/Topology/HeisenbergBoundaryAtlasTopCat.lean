/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat Packaging for the Heisenberg Boundary Atlas

This module realizes the Heisenberg boundary atlas bundle and its parameter base
in `TopCat`, constructs the projection and canonical section morphisms, and proves
the categorical retraction identity `atlasSection ≫ projection = 𝟙 _`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological`:
    `HeisenbergBoundaryAtlasBundle`, `topologicalHeisenbergBoundaryAtlas`.
  * `Mathlib.Topology.Category.TopCat.Basic`: `TopCat.of`, `TopCat.ofHom`.
- BUCKET 2 (Deconfabulation):
  * Both categorical retraction theorems are proved via explicit morphism extensionality
    and unfolding of the section and projection morphisms.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `topCat`, `parameterTopCat`, `projection`, `atlasSection`.
  * `atlasSection_projection`: categorical retraction identity `atlasSection ≫ projection = 𝟙 _`.
  * `atlasSection_projection_apply`: pointwise retraction evaluation on `α : 𝕜`.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasTopCat

open CategoryTheory
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The Heisenberg boundary atlas bundle as a `TopCat` object. -/
abbrev topCat : TopCat :=
  TopCat.of (HeisenbergBoundaryAtlasBundle (𝕜 := 𝕜))

/-- The parameter space of the Heisenberg boundary atlas as a `TopCat` object. -/
abbrev parameterTopCat : TopCat :=
  TopCat.of 𝕜

/-- The canonical projection from the atlas bundle to its parameter base. -/
noncomputable def projection : topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun p => p.1, ?_⟩
  exact continuous_of_discreteTopology

/-- The canonical section of the atlas projection built from `topologicalHeisenbergBoundaryAtlas`. -/
noncomputable def atlasSection : parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun α => topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α, ?_⟩
  exact continuous_of_discreteTopology

/-- Categorical retraction law `atlasSection ≫ projection = 𝟙 _` in `TopCat`. -/
@[simp] theorem atlasSection_projection :
    atlasSection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext α
  unfold atlasSection projection topologicalHeisenbergBoundaryAtlas
  exact Eq.refl _

/-- Pointwise evaluation of the categorical composition `atlasSection ≫ projection` at `α : 𝕜`. -/
@[simp] theorem atlasSection_projection_apply (α : 𝕜) :
    (atlasSection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)) α = α := by
  rw [atlasSection_projection (𝕜 := 𝕜)]
  exact Eq.refl _

end InfoGeometry.Topology.HeisenbergBoundaryAtlasTopCat
