/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological

/-!
# TopCat Packaging for the Finite-Mode Heisenberg Colimit

This module realizes `heisenbergFiniteModeColimit` and `HeisenbergAlgebra 𝕜` in
`TopCat`, constructs the `projection` and `boundarySection` morphisms from the
surjective colimit map, and proves the categorical retraction law
`boundarySection ≫ projection = 𝟙 _`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeColimit`:
    `heisenbergFiniteModeColimit`, `heisenbergFiniteModeColimitMap`.
  * `InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological`:
    `surjective_topologicalHeisenbergFiniteModeColimitMap`.
- BUCKET 2 (Deconfabulation):
  * Categorical retraction and pointwise evaluation are proved via `TopCat.hom_ext`
    and `Classical.choose_spec`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `projection`, `boundarySection`.
  * `projection_boundarySection`: `boundarySection ≫ projection = 𝟙 _`.
  * `projection_boundarySection_apply`: pointwise evaluation on `X : HeisenbergAlgebra 𝕜`.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergFiniteModeColimitTopCat

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical
open VirasoroProject
open InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergFiniteModeColimitTopologicalSpace :
    TopologicalSpace (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeColimitDiscreteTopology :
    DiscreteTopology (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := DiscreteTopology.mk (Eq.refl _)

instance heisenbergAlgebraTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergAlgebraDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := DiscreteTopology.mk (Eq.refl _)

/-- The canonical projection from the finite-mode colimit to the full Heisenberg carrier. -/
noncomputable def projection :
    TopCat.of (heisenbergFiniteModeColimit (𝕜 := 𝕜)) ⟶
      TopCat.of (HeisenbergAlgebra 𝕜) :=
  TopCat.ofHom
    { toFun := heisenbergFiniteModeColimitMap (𝕜 := 𝕜)
      continuous_toFun := continuous_of_discreteTopology }

/-- A canonical section chosen from the surjective finite-mode topological readout. -/
noncomputable def boundarySection :
    TopCat.of (HeisenbergAlgebra 𝕜) ⟶
      TopCat.of (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := by
  refine TopCat.ofHom ?_
  refine ⟨(fun X : HeisenbergAlgebra 𝕜 => ?_), ?_⟩
  · have hsurj :
        ∃ y : ↑(heisenbergFiniteModeColimit (𝕜 := 𝕜)),
          (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom y = X := by
      exact surjective_topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜) X
    exact Classical.choose hsurj
  · exact continuous_of_discreteTopology

/-- Categorical retraction law `boundarySection ≫ projection = 𝟙 _` in `TopCat`. -/
@[simp] theorem projection_boundarySection :
    boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext X
  change (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      (boundarySection (𝕜 := 𝕜) X) = X
  have hsurj :
      ∃ y : ↑(heisenbergFiniteModeColimit (𝕜 := 𝕜)),
        (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom y = X :=
    surjective_topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜) X
  unfold boundarySection
  exact Classical.choose_spec hsurj

/-- Pointwise evaluation of `boundarySection ≫ projection` on `X : HeisenbergAlgebra 𝕜`. -/
@[simp] theorem projection_boundarySection_apply (X : HeisenbergAlgebra 𝕜) :
    (boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)).hom X = X := by
  rw [projection_boundarySection (𝕜 := 𝕜)]
  exact Eq.refl _

end InfoGeometry.Topology.HeisenbergFiniteModeColimitTopCat
