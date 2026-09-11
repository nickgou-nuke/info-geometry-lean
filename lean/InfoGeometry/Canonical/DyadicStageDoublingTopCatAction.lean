import InfoGeometry.Canonical.DyadicStageColimitCompatibleMap
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DyadicStageDirectLimitTopCatCocone
import InfoGeometry.Canonical.DyadicScalarAction
import InfoGeometry.Canonical.DyadicScalarActionLaws

/-!
# Dyadic doubling transported through the stage colimit

The integer-stage doubling map and rational doubling map form an explicit
equivariant natural transformation.  The generic colimit transport theorem
then produces the corresponding intertwining map at the colimit level.
-/

namespace InfoGeometry.Canonical.DyadicStageDoublingTopCatAction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.DyadicDimensionGroupTopCat
open InfoGeometry.Canonical.DyadicStageReadoutTopCat
open InfoGeometry.Canonical.DyadicStageTopCatColimit
open InfoGeometry.Canonical.DyadicStageDirectLimitTopCatCocone
open InfoGeometry.Canonical.DyadicStageColimitCompatibleMap
open InfoGeometry.Canonical.TopCatColimitCompatibleMap
open InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

noncomputable section

def dyadicTwo : DyadicRational :=
  ⟨2, by
    refine ⟨2, 0, ?_⟩
    norm_num⟩

noncomputable def dyadicRationalDoublingTopCatHom :
    dyadicRationalTopCat ⟶ dyadicRationalTopCat :=
  TopCat.ofHom
    { toFun := fun q => dyadicScalarMul dyadicTwo q
      continuous_toFun := by
        exact continuous_dyadicScalarMul.comp
          (continuous_const.prodMk continuous_id) }

noncomputable def dyadicRationalDoublingNat :
    dyadicRationalConstantDiagram ⟶ dyadicRationalConstantDiagram where
  app _ := dyadicRationalDoublingTopCatHom
  naturality := by
    intro i j f
    simp

noncomputable def dyadicStageDoublingNat :
    dyadicStageDiagram ⟶ dyadicStageDiagram :=
  NatTrans.ofSequence
    (app := fun n => dyadicStageTransitionTopCatHom n)
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
      rfl)

theorem dyadicStageDoublingNat_app_eq_transition (n : ℕ) :
    dyadicStageDoublingNat.app n =
      dyadicStageTransitionTopCatHom n := by
  rfl

theorem dyadicStageReadout_doubling_naturality :
    dyadicStageDoublingNat ≫ dyadicStageReadoutCocone.ι =
      dyadicStageReadoutCocone.ι ≫ dyadicRationalDoublingNat := by
  apply NatTrans.ext
  funext n
  apply TopCat.hom_ext
  ext z
  change dyadicStageReadoutCocone.ι.app n
      (dyadicStageDoublingNat.app n z) =
    dyadicRationalDoublingNat.app n
      (dyadicStageReadoutCocone.ι.app n z)
  rw [dyadicStageDoublingNat_app_eq_transition]
  simp only [dyadicStageReadoutCocone_stage,
    dyadicStageTransitionTopCatHom_apply,
    dyadicRationalDoublingNat,
    dyadicRationalDoublingTopCatHom]
  change dyadicStageMap n ((2 : ℤ) * (show ℤ from z)) =
    dyadicScalarMul dyadicTwo (dyadicStageMap n z)
  apply Subtype.ext
  simp [dyadicScalarMul, dyadicTwo, dyadicStageMap]
  ring

theorem dyadicStageReadoutColimitMap_intertwines :
    induced dyadicStageDiagram dyadicStageDoublingNat ≫
        inducedMap dyadicStageReadoutCocone.ι =
      inducedMap dyadicStageReadoutCocone.ι ≫
        induced dyadicRationalConstantDiagram
          dyadicRationalDoublingNat := by
  exact inducedMap_intertwines
      dyadicStageDoublingNat dyadicRationalDoublingNat
      dyadicStageReadoutCocone.ι
      dyadicStageReadout_doubling_naturality

theorem dyadicTwo_smul_stage (n : ℕ) (z : ℤ) :
    dyadicTwo • dyadicStage n z = dyadicStage n (2 * z) := by
  apply dyadicDirectLimitEquiv.injective
  rw [dyadicDirectLimitEquiv_dyadic_smul]
  apply Subtype.ext
  change (2 : ℚ) *
      ((dyadicStageMap n z : DyadicRational) : ℚ) =
    ((dyadicStageMap n (2 * z) : DyadicRational) : ℚ)
  simp [dyadicStageMap]
  ring

noncomputable def dyadicDirectLimitScalarTopCatHom (a : DyadicRational) :
    dyadicDirectLimitTopCat ⟶ dyadicDirectLimitTopCat :=
  TopCat.ofHom
    { toFun := fun x => a • x
      continuous_toFun := by
        exact continuous_dyadicDirectLimit_dyadic_smul.comp
          (continuous_const.prodMk continuous_id) }

noncomputable def dyadicDirectLimitDoublingTopCatHom :
    dyadicDirectLimitTopCat ⟶ dyadicDirectLimitTopCat :=
  dyadicDirectLimitScalarTopCatHom dyadicTwo

@[simp] theorem dyadicDirectLimitScalarTopCatHom_apply
    (a : DyadicRational) (x : DyadicDirectLimit) :
    dyadicDirectLimitScalarTopCatHom a x = a • x := rfl

theorem dyadicDirectLimitScalarTopCatHom_one :
    dyadicDirectLimitScalarTopCatHom dyadicOne =
      𝟙 dyadicDirectLimitTopCat := by
  apply TopCat.hom_ext
  ext x
  exact dyadicDirectLimit_dyadic_smul_one x

theorem dyadicDirectLimitScalarTopCatHom_comp
    (a b : DyadicRational) :
    dyadicDirectLimitScalarTopCatHom a ≫
        dyadicDirectLimitScalarTopCatHom b =
      dyadicDirectLimitScalarTopCatHom
        (dyadicScalarMul b a) := by
  apply TopCat.hom_ext
  ext x
  change b • (a • (show DyadicDirectLimit from x)) =
    dyadicScalarMul b a • (show DyadicDirectLimit from x)
  simpa using
    (dyadicDirectLimit_dyadic_smul_assoc b a
      (show DyadicDirectLimit from x))

theorem dyadicDirectLimitScalarTopCatHom_unique
    (a : DyadicRational)
    (g : dyadicDirectLimitTopCat ⟶ dyadicDirectLimitTopCat)
    (hg : ∀ (n : ℕ) (z : ℤ),
      g (dyadicStage n z) = a • dyadicStage n z) :
    g = dyadicDirectLimitScalarTopCatHom a := by
  apply TopCat.hom_ext
  ext x
  induction x using Quotient.inductionOn with
  | _ rep =>
      rcases rep with ⟨z, n⟩
      exact hg n z

theorem dyadicDirectLimitDoubling_stage_square (n : ℕ) :
    dyadicStageTransitionTopCatHom n ≫
        dyadicDirectLimitStageTopCatHom n =
      dyadicDirectLimitStageTopCatHom n ≫
        dyadicDirectLimitDoublingTopCatHom := by
  apply TopCat.hom_ext
  ext z
  exact (dyadicTwo_smul_stage n z).symm

theorem dyadicStageDoubling_descends_to_directLimit :
    induced dyadicStageDiagram dyadicStageDoublingNat ≫
        dyadicStageColimitToDirectLimit =
      dyadicStageColimitToDirectLimit ≫
        dyadicDirectLimitDoublingTopCatHom := by
  apply colimit.hom_ext
  intro n
  calc
    colimit.ι dyadicStageDiagram n ≫
          induced dyadicStageDiagram dyadicStageDoublingNat ≫
            dyadicStageColimitToDirectLimit =
        (colimit.ι dyadicStageDiagram n ≫
          induced dyadicStageDiagram dyadicStageDoublingNat) ≫
            dyadicStageColimitToDirectLimit :=
      (Category.assoc _ _ _).symm
    _ = (dyadicStageDoublingNat.app n ≫
          colimit.ι dyadicStageDiagram n) ≫
            dyadicStageColimitToDirectLimit := by
      rw [induced_on_stage]
    _ = dyadicStageDoublingNat.app n ≫
          (colimit.ι dyadicStageDiagram n ≫
            dyadicStageColimitToDirectLimit) :=
      Category.assoc _ _ _
    _ = dyadicStageDoublingNat.app n ≫
          dyadicDirectLimitStageCocone.ι.app n := by
      rw [dyadicStageColimitToDirectLimit_stage]
    _ = dyadicStageTransitionTopCatHom n ≫
          dyadicDirectLimitStageTopCatHom n := by
      rw [dyadicStageDoublingNat_app_eq_transition]
      rfl
    _ = dyadicDirectLimitStageTopCatHom n ≫
          dyadicDirectLimitDoublingTopCatHom :=
      dyadicDirectLimitDoubling_stage_square n
    _ = (colimit.ι dyadicStageDiagram n ≫
          dyadicStageColimitToDirectLimit) ≫
            dyadicDirectLimitDoublingTopCatHom := by
      rw [dyadicStageColimitToDirectLimit_stage]
      rfl
    _ = colimit.ι dyadicStageDiagram n ≫
          (dyadicStageColimitToDirectLimit ≫
            dyadicDirectLimitDoublingTopCatHom) :=
      Category.assoc _ _ _

end
end InfoGeometry.Canonical.DyadicStageDoublingTopCatAction
