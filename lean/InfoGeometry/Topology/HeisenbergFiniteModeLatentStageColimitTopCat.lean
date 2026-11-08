/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological

/-!
# TopCat Colimit of Finite Heisenberg Latent Stages

This module constructs the functor `latentStageDiagram q : Finset (Option ℤ) ⥤ TopCat`
sending each finite mode subset `s` to `TopCat.of (heisenbergFiniteModeStageLatentSet q s)`,
constructs the cocone `latentStageRangeCocone q` with vertex `TopCat.of (LatentLabelRange q)`,
and proves that the induced colimit comparison morphism `latentStageColimitReadout q`
commutes stagewise, is surjective, and satisfies the universal uniqueness property.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological`:
    `heisenbergFiniteModeStageLatentSet`, `heisenbergFiniteModeStageLatentSet_mono`.
- BUCKET 2 (Deconfabulation):
  * Stage commutation, surjectivity, and colimit uniqueness are proved constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `LatentLabelRange`, `latentStageInclusion`, `latentStageDiagram`,
    `latentStageToRange`, `latentStageRangeCocone`, `latentStageColimitReadout`.
  * `latentStageColimitReadout_stage`, `latentStageColimitReadout_surjective`,
    `latentStageColimitReadout_unique`.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeLatentStageColimitTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
open InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Range of all basis-index latent labels at sixth-root parameter `q`. -/
abbrev LatentLabelRange (q : SixthRootParameter) :=
  Set.range (fun i : Option ℤ =>
    heisenbergFiniteModeLatentReadout (q, i))

/-- Inclusion morphism in `TopCat` between finite-stage latent subsets for `s ⊆ t`. -/
def latentStageInclusion
    (q : SixthRootParameter) {s t : Finset (Option ℤ)}
    (hst : s ⊆ t) :
    TopCat.of (heisenbergFiniteModeStageLatentSet q s) ⟶
      TopCat.of (heisenbergFiniteModeStageLatentSet q t) :=
  TopCat.ofHom <| ContinuousMap.mk
    (fun z => ⟨z.1, heisenbergFiniteModeStageLatentSet_mono q hst z.2⟩)
    continuous_of_discreteTopology

/-- Functor from `Finset (Option ℤ)` to `TopCat` sending `s` to its finite-stage latent subset. -/
def latentStageDiagram (q : SixthRootParameter) :
    Finset (Option ℤ) ⥤ TopCat where
  obj s := TopCat.of (heisenbergFiniteModeStageLatentSet q s)
  map f := latentStageInclusion q f.down.down
  map_id _s := by
    apply TopCat.hom_ext
    ext z
    unfold latentStageInclusion
    exact Eq.refl _
  map_comp _f _g := by
    apply TopCat.hom_ext
    ext z
    unfold latentStageInclusion
    exact Eq.refl _

/-- Inclusion morphism in `TopCat` from a finite-stage latent subset into `LatentLabelRange q`. -/
def latentStageToRange
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    TopCat.of (heisenbergFiniteModeStageLatentSet q s) ⟶
      TopCat.of (LatentLabelRange q) :=
  TopCat.ofHom <| ContinuousMap.mk
    (fun z => ⟨z.1, by
      change z.1 ∈ Set.range (fun i : Option ℤ =>
        heisenbergFiniteModeLatentReadout (q, i))
      have hz : z.1 ∈ heisenbergFiniteModeStageLatentSet q s := z.2
      change z.1 ∈ heisenbergFiniteModeStageLatentImage q s at hz
      rcases Finset.mem_image.mp hz with ⟨i, _hi, hzi⟩
      exact ⟨i, hzi⟩⟩)
    continuous_of_discreteTopology

/-- Cocone over `latentStageDiagram q` with vertex `TopCat.of (LatentLabelRange q)`. -/
def latentStageRangeCocone (q : SixthRootParameter) :
    Cocone (latentStageDiagram q) where
  pt := TopCat.of (LatentLabelRange q)
  ι := {
    app := latentStageToRange q
    naturality := by
      intro _s _t _f
      apply TopCat.hom_ext
      ext z
      unfold latentStageDiagram latentStageInclusion latentStageToRange
      exact Eq.refl _ }

/-- Colimit comparison morphism from `colimit (latentStageDiagram q)` to `TopCat.of (LatentLabelRange q)`. -/
noncomputable def latentStageColimitReadout (q : SixthRootParameter) :
    colimit (latentStageDiagram q) ⟶ TopCat.of (LatentLabelRange q) :=
  colimit.desc (latentStageDiagram q) (latentStageRangeCocone q)

/-- Stagewise factorization of `latentStageColimitReadout q` through `latentStageRangeCocone q`. -/
theorem latentStageColimitReadout_stage
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    colimit.ι (latentStageDiagram q) s ≫
        latentStageColimitReadout q =
      (latentStageRangeCocone q).ι.app s := by
  unfold latentStageColimitReadout
  exact colimit.ι_desc (latentStageRangeCocone q) s

/-- Surjectivity of the colimit comparison map `latentStageColimitReadout q`. -/
theorem latentStageColimitReadout_surjective
    (q : SixthRootParameter) :
    Function.Surjective (latentStageColimitReadout q) := by
  intro z
  rcases z.2 with ⟨i, hi⟩
  let s : Finset (Option ℤ) := {i}
  let x : (latentStageDiagram q).obj s :=
    ⟨heisenbergFiniteModeLatentReadout (q, i), by
      change heisenbergFiniteModeLatentReadout (q, i) ∈
        heisenbergFiniteModeStageLatentImage q s
      exact Finset.mem_image.mpr ⟨i, Finset.mem_singleton_self i, Eq.refl _⟩⟩
  refine ⟨(colimit.ι (latentStageDiagram q) s) x, ?_⟩
  have hstage := latentStageColimitReadout_stage q s
  have hstage' :
      latentStageColimitReadout q ((colimit.ι (latentStageDiagram q) s) x) =
        ((latentStageRangeCocone q).ι.app s) x := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun f => f x) hstage
  rw [hstage']
  apply Subtype.ext
  exact hi

/-- Universal uniqueness of morphisms out of `colimit (latentStageDiagram q)` agreeing on all stages. -/
theorem latentStageColimitReadout_unique
    (q : SixthRootParameter)
    {u v : colimit (latentStageDiagram q) ⟶ TopCat.of (LatentLabelRange q)}
    (hu : ∀ s, colimit.ι (latentStageDiagram q) s ≫ u =
      (latentStageRangeCocone q).ι.app s)
    (hv : ∀ s, colimit.ι (latentStageDiagram q) s ≫ v =
      (latentStageRangeCocone q).ι.app s) :
    u = v := by
  apply colimit.hom_ext
  intro s
  rw [hu s, hv s]

end
end InfoGeometry.Topology.HeisenbergFiniteModeLatentStageColimitTopCat
