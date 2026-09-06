import InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
import InfoGeometry.Krein.HestenesKreinFinite

/-!
# Concrete constant finite-stage two-sheet system

This is the smallest honest stage system: every stage is the native finite
Hestenes sheet matrix carrier and every transition map is the identity.  It is
used to validate the categorical transport before introducing a nontrivial
stage tower.
-/

noncomputable section

namespace InfoGeometry.Categorical.TwoSheetKreinStageSystem

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.ChiralStokesPauliBasis
open InfoGeometry.Krein.HestenesKreinFinite

abbrev Carrier := Sheet

abbrev StageFunctor : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj (ModuleCat.of ℝ Carrier)

def constantEndNatTrans (T : Carrier →ₗ[ℝ] Carrier) :
    StageFunctor ⟶ StageFunctor :=
  NatTrans.ofSequence
    (fun _ => ModuleCat.ofHom T)
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      rfl)

def kreinAction : Carrier →ₗ[ℝ] Carrier :=
  (LinearMap.mulLeft ℝ fundamentalSymmetry).comp
    (LinearMap.mulRight ℝ fundamentalSymmetry)

def plusAction : Carrier →ₗ[ℝ] Carrier :=
  LinearMap.mulLeft ℝ fPlus

def minusAction : Carrier →ₗ[ℝ] Carrier :=
  LinearMap.mulLeft ℝ fMinus

def kreinStage : StageFunctor ⟶ StageFunctor :=
  constantEndNatTrans kreinAction

def plusStage : StageFunctor ⟶ StageFunctor :=
  constantEndNatTrans plusAction

def minusStage : StageFunctor ⟶ StageFunctor :=
  constantEndNatTrans minusAction

theorem kreinAction_square :
    kreinAction.comp kreinAction = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change fundamentalSymmetry *
      (fundamentalSymmetry * (x * fundamentalSymmetry) * fundamentalSymmetry) = x
  calc
    fundamentalSymmetry *
          (fundamentalSymmetry * (x * fundamentalSymmetry) * fundamentalSymmetry) =
        (fundamentalSymmetry * fundamentalSymmetry) * x *
          (fundamentalSymmetry * fundamentalSymmetry) := by
            simp only [mul_assoc]
    _ = x := by rw [fundamentalSymmetry_sq]; simp

theorem kreinStage_square :
    kreinStage ≫ kreinStage = 𝟙 StageFunctor := by
  ext n x
  simpa [kreinStage, constantEndNatTrans, ModuleCat.comp_apply] using
    congrArg (fun y => y x) kreinAction_square

theorem kreinStage_exchanges_plus :
    kreinStage ≫ plusStage ≫ kreinStage = minusStage := by
  ext n x
  dsimp [StageFunctor] at x ⊢
  change fundamentalSymmetry *
      (fPlus * (fundamentalSymmetry * ((x : Carrier) * fundamentalSymmetry)) *
        fundamentalSymmetry) = fMinus * (x : Carrier)
  calc
    fundamentalSymmetry *
          (fPlus * (fundamentalSymmetry * ((x : Carrier) * fundamentalSymmetry)) *
            fundamentalSymmetry) =
        (fundamentalSymmetry * fPlus * fundamentalSymmetry) *
          (x : Carrier) * (fundamentalSymmetry * fundamentalSymmetry) := by
            simp only [mul_assoc]
    _ = fMinus * (x : Carrier) := by
      rw [fundamentalSymmetry_fPlus_fundamentalSymmetry,
        fundamentalSymmetry_sq]
      simp

def twoSheetColimitEnd (s : StageFunctor ⟶ StageFunctor) :
    Module.End ℝ
      (InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.Carrier StageFunctor) :=
  InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd s

theorem twoSheetColimit_krein_square :
    twoSheetColimitEnd kreinStage * twoSheetColimitEnd kreinStage =
      LinearMap.id := by
  exact InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd_involutive
    kreinStage kreinStage_square

theorem twoSheetColimit_krein_exchanges_plus :
    twoSheetColimitEnd kreinStage * twoSheetColimitEnd plusStage *
        twoSheetColimitEnd kreinStage = twoSheetColimitEnd minusStage := by
  exact InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd_exchange
    kreinStage plusStage minusStage kreinStage_exchanges_plus

end InfoGeometry.Categorical.TwoSheetKreinStageSystem
