import InfoGeometry.Canonical.DyadicStageTopCatColimit

namespace InfoGeometry.Canonical.DyadicStageDirectLimitTopCatCocone

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.DyadicDimensionGroupTopCat
open InfoGeometry.Canonical.DyadicStageReadoutTopCat
open InfoGeometry.Canonical.DyadicStageTopCatColimit

noncomputable section

def dyadicDirectLimitStageTopCatHom (n : ℕ) :
    TopCat.of ℤ ⟶ dyadicDirectLimitTopCat :=
  TopCat.ofHom
    { toFun := dyadicStage n
      continuous_toFun := by
        exact continuous_of_discreteTopology }

def dyadicDirectLimitStageCocone : Cocone dyadicStageDiagram where
  pt := dyadicDirectLimitTopCat
  ι := NatTrans.ofSequence
    (app := fun n => dyadicDirectLimitStageTopCatHom n)
    (naturality := by
      intro n
      have hmap :
          dyadicStageDiagram.map (homOfLE (Nat.le_succ n)) =
            dyadicStageTransitionTopCatHom n := by
        simpa [dyadicStageDiagram] using
          (Functor.ofSequence_map_homOfLE_succ
            (f := fun n => dyadicStageTransitionTopCatHom n) n)
      rw [hmap]
      apply TopCat.hom_ext
      ext z
      simpa [dyadicBond] using dyadicStage_bond n z)

noncomputable def dyadicStageColimitToDirectLimit :
    dyadicStageTopCatColimit ⟶ dyadicDirectLimitTopCat :=
  colimit.desc dyadicStageDiagram dyadicDirectLimitStageCocone

theorem dyadicStageColimitToDirectLimit_stage (n : ℕ) :
    colimit.ι dyadicStageDiagram n ≫
        dyadicStageColimitToDirectLimit =
      dyadicDirectLimitStageCocone.ι.app n := by
  exact colimit.ι_desc dyadicDirectLimitStageCocone n

theorem dyadicDirectLimitStageCocone_apply (n : ℕ) (z : ℤ) :
    dyadicDirectLimitStageCocone.ι.app n z = dyadicStage n z := rfl

theorem dyadicStageColimitReadout_factors_through_directLimit :
    dyadicStageColimitToDirectLimit ≫
        dyadicDirectLimitReadoutTopCatHom =
      dyadicStageColimitReadout := by
  apply colimit.hom_ext
  intro n
  rw [← Category.assoc, dyadicStageColimitToDirectLimit_stage]
  rw [dyadicStageColimitReadout_stage]
  apply TopCat.hom_ext
  ext z
  rfl

theorem dyadicStageColimitToDirectLimit_surjective :
    Function.Surjective
      (dyadicStageColimitToDirectLimit.hom :
        dyadicStageTopCatColimit → dyadicDirectLimitTopCat) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ rep =>
      rcases rep with ⟨z, n⟩
      refine ⟨colimit.ι dyadicStageDiagram n z, ?_⟩
      have hstage := congrArg (fun f => f z)
        (dyadicStageColimitToDirectLimit_stage n)
      exact hstage

end
end InfoGeometry.Canonical.DyadicStageDirectLimitTopCatCocone
