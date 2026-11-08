import InfoGeometry.Canonical.DyadicStageReadoutTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.DyadicStageTopCatColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.DyadicDimensionGroupTopCat
open InfoGeometry.Canonical.DyadicStageReadoutTopCat

noncomputable section

def dyadicStageDiagram : ℕ ⥤ TopCat :=
  Functor.ofSequence (X := fun _ => TopCat.of ℤ)
    (fun n => dyadicStageTransitionTopCatHom n)

def dyadicStageReadoutCocone : Cocone dyadicStageDiagram where
  pt := dyadicRationalTopCat
  ι := NatTrans.ofSequence
    (app := fun n => dyadicStageReadoutTopCatHom n)
    (naturality := by
      intro n
      have hmap :
          dyadicStageDiagram.map (homOfLE (Nat.le_succ n)) =
            dyadicStageTransitionTopCatHom n := by
        simpa [dyadicStageDiagram] using
          (Functor.ofSequence_map_homOfLE_succ
            (f := fun n => dyadicStageTransitionTopCatHom n) n)
      rw [hmap]
      exact dyadicStageReadoutTopCatHom_compatibility n)

abbrev dyadicStageTopCatColimit : TopCat :=
  colimit dyadicStageDiagram

noncomputable def dyadicStageColimitReadout :
    dyadicStageTopCatColimit ⟶ dyadicRationalTopCat :=
  colimit.desc dyadicStageDiagram dyadicStageReadoutCocone

theorem dyadicStageColimitReadout_stage (n : ℕ) :
    colimit.ι dyadicStageDiagram n ≫ dyadicStageColimitReadout =
      dyadicStageReadoutCocone.ι.app n := by
  exact colimit.ι_desc dyadicStageReadoutCocone n

theorem dyadicStageReadoutCocone_stage (n : ℕ) (z : ℤ) :
    dyadicStageReadoutCocone.ι.app n z = dyadicStageMap n z := rfl

theorem dyadicStageColimitReadout_unique
    {u v : dyadicStageTopCatColimit ⟶ dyadicRationalTopCat}
    (h : ∀ n : ℕ,
      colimit.ι dyadicStageDiagram n ≫ u =
        colimit.ι dyadicStageDiagram n ≫ v) :
    u = v := by
  apply colimit.hom_ext
  intro n
  exact h n

theorem dyadicStageColimitReadout_surjective :
    Function.Surjective
      (dyadicStageColimitReadout.hom :
        dyadicStageTopCatColimit → dyadicRationalTopCat) := by
  intro q
  rcases q.property with ⟨z, n, hq⟩
  let z' : dyadicStageDiagram.obj n := z
  refine ⟨colimit.ι dyadicStageDiagram n z', ?_⟩
  have hstage := congrArg (fun f => f z')
    (dyadicStageColimitReadout_stage n)
  change dyadicStageColimitReadout (colimit.ι dyadicStageDiagram n z') =
    (dyadicStageReadoutCocone.ι.app n) z' at hstage
  rw [dyadicStageReadoutCocone_stage] at hstage
  change dyadicStageColimitReadout
      (colimit.ι dyadicStageDiagram n z') = q
  rw [hstage]
  apply Subtype.ext
  simpa [z', dyadicStageMap] using hq.symm

end
end InfoGeometry.Canonical.DyadicStageTopCatColimit
