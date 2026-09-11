import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological

/-!
# TopCat colimit of finite Heisenberg latent stages

The finite clopen latent stages form a genuine `TopCat` diagram indexed by
finite mode subsets.  Its cocone lands in the exact subtype of latent labels
that occur, and the induced colimit readout is proved stagewise and
surjectively.  No claim is made that this range equals the ambient latent
quotient.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeLatentStageColimitTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
open InfoGeometry.Topology.HeisenbergFiniteModeLatentStageUnionTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

abbrev LatentLabelRange (q : SixthRootParameter) :=
  Set.range (fun i : Option ℤ =>
    heisenbergFiniteModeLatentReadout (q, i))

def latentStageInclusion
    (q : SixthRootParameter) {s t : Finset (Option ℤ)}
    (hst : s ⊆ t) :
    TopCat.of (heisenbergFiniteModeStageLatentSet q s) ⟶
      TopCat.of (heisenbergFiniteModeStageLatentSet q t) :=
  TopCat.ofHom <| ContinuousMap.mk
    (fun z => ⟨z.1, heisenbergFiniteModeStageLatentSet_mono q hst z.2⟩)
    continuous_of_discreteTopology

def latentStageDiagram (q : SixthRootParameter) :
    Finset (Option ℤ) ⥤ TopCat where
  obj s := TopCat.of (heisenbergFiniteModeStageLatentSet q s)
  map f := latentStageInclusion q f.down.down
  map_id s := by
    apply TopCat.hom_ext
    ext z <;> simp [latentStageInclusion]
  map_comp f g := by
    apply TopCat.hom_ext
    ext z <;> simp [latentStageInclusion]

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
      rcases Finset.mem_image.mp hz with ⟨i, hi, hzi⟩
      exact ⟨i, hzi⟩⟩)
    continuous_of_discreteTopology

def latentStageRangeCocone (q : SixthRootParameter) :
    Cocone (latentStageDiagram q) where
  pt := TopCat.of (LatentLabelRange q)
  ι := {
    app := latentStageToRange q
    naturality := by
      intro s t f
      apply TopCat.hom_ext
      ext z
      rfl }

noncomputable def latentStageColimitReadout (q : SixthRootParameter) :
    colimit (latentStageDiagram q) ⟶ TopCat.of (LatentLabelRange q) :=
  colimit.desc (latentStageDiagram q) (latentStageRangeCocone q)

theorem latentStageColimitReadout_stage
    (q : SixthRootParameter) (s : Finset (Option ℤ)) :
    colimit.ι (latentStageDiagram q) s ≫
        latentStageColimitReadout q =
      (latentStageRangeCocone q).ι.app s := by
  exact colimit.ι_desc (latentStageRangeCocone q) s

theorem latentStageColimitReadout_surjective
    (q : SixthRootParameter) :
    Function.Surjective (latentStageColimitReadout q) := by
  intro z
  rcases z.2 with ⟨i, hi⟩
  let s : Finset (Option ℤ) := {i}
  let x : heisenbergFiniteModeStageLatentSet q s :=
    ⟨heisenbergFiniteModeLatentReadout (q, i), by
      change heisenbergFiniteModeLatentReadout (q, i) ∈
        heisenbergFiniteModeStageLatentImage q s
      exact Finset.mem_image.mpr ⟨i, by simp [s], rfl⟩⟩
  refine ⟨(colimit.ι (latentStageDiagram q) s) x, ?_⟩
  have hstage := latentStageColimitReadout_stage q s
  have hstage' := congrArg (fun f => f x) hstage
  calc
    (latentStageColimitReadout q) ((colimit.ι (latentStageDiagram q) s) x) =
        ((latentStageRangeCocone q).ι.app s) x := hstage'
    _ = z := by
      apply Subtype.ext
      exact hi

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
