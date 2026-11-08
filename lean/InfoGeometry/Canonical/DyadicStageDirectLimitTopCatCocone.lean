import InfoGeometry.Canonical.DyadicStageTopCatColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
      change ℤ at z
      change dyadicStage (n + 1) (2 * z) = dyadicStage n z
      exact dyadicStage_bond n z)

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
  apply TopCat.hom_ext
  ext z
  have hleft := congrArg (fun f => f z)
    (dyadicStageColimitToDirectLimit_stage n)
  change dyadicStageColimitToDirectLimit
      (colimit.ι dyadicStageDiagram n z) =
    (dyadicDirectLimitStageCocone.ι.app n) z at hleft
  change dyadicStageColimitToDirectLimit
      (colimit.ι dyadicStageDiagram n z) = dyadicStage n z at hleft
  have hright := congrArg (fun f => f z)
    (dyadicStageColimitReadout_stage n)
  change dyadicStageColimitReadout
      (colimit.ι dyadicStageDiagram n z) =
    (dyadicStageReadoutCocone.ι.app n) z at hright
  change dyadicStageColimitReadout
      (colimit.ι dyadicStageDiagram n z) = dyadicStageMap n z at hright
  change dyadicDirectLimitReadoutTopCatHom
      (dyadicStageColimitToDirectLimit
        (colimit.ι dyadicStageDiagram n z)) =
    dyadicStageColimitReadout (colimit.ι dyadicStageDiagram n z)
  rw [hleft, hright]
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
      change dyadicStageColimitToDirectLimit
          (colimit.ι dyadicStageDiagram n z) =
        (dyadicDirectLimitStageCocone.ι.app n) z at hstage
      rw [dyadicDirectLimitStageCocone_apply] at hstage
      change dyadicStageColimitToDirectLimit
          (colimit.ι dyadicStageDiagram n z) = Quotient.mk' ⟨z, n⟩
      rw [hstage]
      rfl

end
end InfoGeometry.Canonical.DyadicStageDirectLimitTopCatCocone
