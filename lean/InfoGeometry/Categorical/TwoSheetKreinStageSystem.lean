/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.HestenesKreinFinite
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge

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

abbrev StageFunctor : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj
    (ModuleCat.of ℝ InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix)

def constantEndNatTrans
    (T : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix →ₗ[ℝ]
      InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) :
    StageFunctor ⟶ StageFunctor :=
  NatTrans.ofSequence
    (fun _ => ModuleCat.ofHom T)
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      rfl)

def kreinAction :
    InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix →ₗ[ℝ]
      InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix :=
  (LinearMap.mulLeft ℝ fundamentalSymmetry).comp
    (LinearMap.mulRight ℝ fundamentalSymmetry)

def plusAction :
    InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix →ₗ[ℝ]
      InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix :=
  LinearMap.mulLeft ℝ fPlus

def minusAction :
    InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix →ₗ[ℝ]
      InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix :=
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
      (fPlus * (fundamentalSymmetry *
        ((x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) *
          fundamentalSymmetry)) * fundamentalSymmetry) =
        fMinus * (x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix)
  calc
    fundamentalSymmetry *
          (fPlus * (fundamentalSymmetry *
            ((x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) *
              fundamentalSymmetry)) * fundamentalSymmetry) =
        (fundamentalSymmetry * fPlus * fundamentalSymmetry) *
          (x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) *
            (fundamentalSymmetry * fundamentalSymmetry) := by
            simp only [mul_assoc]
    _ = fMinus * (x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) := by
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

/-! ## 2. Two-Sheet Hestenes–Krein Bridge to the Peirce Spine and Filtered Colimit -/

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian

theorem plusStage_idempotent :
    plusStage ≫ plusStage = plusStage := by
  ext n x
  dsimp [StageFunctor] at x ⊢
  change fPlus * (fPlus * (x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix)) =
    fPlus * (x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix)
  rw [← mul_assoc, fPlus_idempotent]

theorem twoSheetColimit_plus_idempotent :
    twoSheetColimitEnd plusStage * twoSheetColimitEnd plusStage =
      twoSheetColimitEnd plusStage := by
  unfold twoSheetColimitEnd
  rw [← InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd_comp,
    plusStage_idempotent]

/-- **Finite-Stage & Filtered-Colimit Two-Sheet Krein $\leftrightarrow$ Peirce Spine Bridge**:
1. On `SheetMatrix`, `fPlus` is a Peirce idempotent (`fPlus * fPlus = fPlus`) with complementary
   projector `1 - fPlus = fMinus`, satisfying the pinching–defect law
   `evenGrade fPlus (idempotencyDefect X) - idempotencyDefect (evenGrade fPlus X) = genV fPlus X X`;
2. Conjugating by the Krein fundamental symmetry (`kreinAction X = J * X * J`) exchanges the
   two Peirce corners (`kreinAction (peirce11 fPlus X) = peirce00 fPlus (kreinAction X)`) and
   swaps the upper and lower Peirce corner cycles (`kreinAction (qgtPlus fPlus A C) = qgtMinus fPlus (kreinAction C) (kreinAction A)`),
   preserving `genV`: `kreinAction (genV fPlus A C) = genV fPlus (kreinAction C) (kreinAction A)`;
3. In the filtered colimit `Module.End ℝ (Carrier StageFunctor)`, `P_colim = twoSheetColimitEnd plusStage`
   is an exact Peirce idempotent satisfying the Peirce pinching–defect law and Maurer–Cartan
   self-dual Yang–Mills identity `peirceCovariantDeriv P_colim A_colim C_colim (genV P_colim A_colim C_colim) = 0`. -/
theorem twoSheetKrein_peirce_spine_and_colimit_bridge
    (X A C : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix)
    (X_colim A_colim C_colim :
      Module.End ℝ (InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.Carrier StageFunctor)) :
    let P_colim := twoSheetColimitEnd plusStage
    1 - fPlus = fMinus ∧
    evenGrade fPlus (idempotencyDefect X) - idempotencyDefect (evenGrade fPlus X) =
      genV fPlus X X ∧
    kreinAction (peirce11 fPlus X) = peirce00 fPlus (kreinAction X) ∧
    kreinAction (qgtPlus fPlus A C) = qgtMinus fPlus (kreinAction C) (kreinAction A) ∧
    kreinAction (genV fPlus A C) = genV fPlus (kreinAction C) (kreinAction A) ∧
    P_colim * P_colim = P_colim ∧
    evenGrade P_colim (idempotencyDefect X_colim) -
        idempotencyDefect (evenGrade P_colim X_colim) =
      genV P_colim X_colim X_colim ∧
    peirceCovariantDeriv P_colim A_colim C_colim (genV P_colim A_colim C_colim) = 0 := by
  dsimp only
  have hComp : (1 : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) - fPlus = fMinus :=
    sub_eq_of_eq_add' fPlus_add_fMinus.symm
  have hJ2 : fundamentalSymmetry * fundamentalSymmetry = 1 := fundamentalSymmetry_sq
  have hJfP : fundamentalSymmetry * fPlus * fundamentalSymmetry = fMinus :=
    fundamentalSymmetry_fPlus_fundamentalSymmetry
  have hJfM : fundamentalSymmetry * fMinus * fundamentalSymmetry = fPlus :=
    fundamentalSymmetry_fMinus_fundamentalSymmetry
  have hKreinMul : ∀ Y Z, kreinAction (Y * Z) = kreinAction Y * kreinAction Z := by
    intro Y Z
    change fundamentalSymmetry * ((Y * Z) * fundamentalSymmetry) =
      (fundamentalSymmetry * (Y * fundamentalSymmetry)) *
        (fundamentalSymmetry * (Z * fundamentalSymmetry))
    calc
      fundamentalSymmetry * ((Y * Z) * fundamentalSymmetry) =
          fundamentalSymmetry * Y * (fundamentalSymmetry * fundamentalSymmetry) *
            Z * fundamentalSymmetry := by
        rw [hJ2]; noncomm_ring
      _ = (fundamentalSymmetry * (Y * fundamentalSymmetry)) *
            (fundamentalSymmetry * (Z * fundamentalSymmetry)) := by
        noncomm_ring
  have hKreinCP : ∀ Y, kreinAction (conePlus fPlus Y) = coneMinus fPlus (kreinAction Y) := by
    intro Y
    change fundamentalSymmetry * ((fPlus * Y * (1 - fPlus)) * fundamentalSymmetry) =
      (1 - fPlus) * (fundamentalSymmetry * (Y * fundamentalSymmetry)) * fPlus
    rw [hComp]
    calc
      fundamentalSymmetry * ((fPlus * Y * fMinus) * fundamentalSymmetry) =
          (fundamentalSymmetry * fPlus * fundamentalSymmetry) *
            (fundamentalSymmetry * (Y * fundamentalSymmetry)) *
            (fundamentalSymmetry * fMinus * fundamentalSymmetry) := by
        calc
          fundamentalSymmetry * ((fPlus * Y * fMinus) * fundamentalSymmetry) =
              fundamentalSymmetry * fPlus * (fundamentalSymmetry * fundamentalSymmetry) *
                Y * (fundamentalSymmetry * fundamentalSymmetry) *
                fMinus * fundamentalSymmetry := by
            rw [hJ2]; noncomm_ring
          _ = (fundamentalSymmetry * fPlus * fundamentalSymmetry) *
                (fundamentalSymmetry * (Y * fundamentalSymmetry)) *
                (fundamentalSymmetry * fMinus * fundamentalSymmetry) := by
            noncomm_ring
      _ = fMinus * (fundamentalSymmetry * (Y * fundamentalSymmetry)) * fPlus := by
        rw [hJfP, hJfM]
  have hKreinCM : ∀ Y, kreinAction (coneMinus fPlus Y) = conePlus fPlus (kreinAction Y) := by
    intro Y
    change fundamentalSymmetry * (((1 - fPlus) * Y * fPlus) * fundamentalSymmetry) =
      fPlus * (fundamentalSymmetry * (Y * fundamentalSymmetry)) * (1 - fPlus)
    rw [hComp]
    calc
      fundamentalSymmetry * ((fMinus * Y * fPlus) * fundamentalSymmetry) =
          (fundamentalSymmetry * fMinus * fundamentalSymmetry) *
            (fundamentalSymmetry * (Y * fundamentalSymmetry)) *
            (fundamentalSymmetry * fPlus * fundamentalSymmetry) := by
        calc
          fundamentalSymmetry * ((fMinus * Y * fPlus) * fundamentalSymmetry) =
              fundamentalSymmetry * fMinus * (fundamentalSymmetry * fundamentalSymmetry) *
                Y * (fundamentalSymmetry * fundamentalSymmetry) *
                fPlus * fundamentalSymmetry := by
            rw [hJ2]; noncomm_ring
          _ = (fundamentalSymmetry * fMinus * fundamentalSymmetry) *
                (fundamentalSymmetry * (Y * fundamentalSymmetry)) *
                (fundamentalSymmetry * fPlus * fundamentalSymmetry) := by
            noncomm_ring
      _ = fPlus * (fundamentalSymmetry * (Y * fundamentalSymmetry)) * fMinus := by
        rw [hJfM, hJfP]
  have hKrein11 : kreinAction (peirce11 fPlus X) = peirce00 fPlus (kreinAction X) := by
    change fundamentalSymmetry * ((fPlus * X * fPlus) * fundamentalSymmetry) =
      (1 - fPlus) * (fundamentalSymmetry * (X * fundamentalSymmetry)) * (1 - fPlus)
    rw [hComp]
    calc
      fundamentalSymmetry * ((fPlus * X * fPlus) * fundamentalSymmetry) =
          (fundamentalSymmetry * fPlus * fundamentalSymmetry) *
            (fundamentalSymmetry * (X * fundamentalSymmetry)) *
            (fundamentalSymmetry * fPlus * fundamentalSymmetry) := by
        calc
          fundamentalSymmetry * ((fPlus * X * fPlus) * fundamentalSymmetry) =
              fundamentalSymmetry * fPlus * (fundamentalSymmetry * fundamentalSymmetry) *
                X * (fundamentalSymmetry * fundamentalSymmetry) *
                fPlus * fundamentalSymmetry := by
            rw [hJ2]; noncomm_ring
          _ = (fundamentalSymmetry * fPlus * fundamentalSymmetry) *
                (fundamentalSymmetry * (X * fundamentalSymmetry)) *
                (fundamentalSymmetry * fPlus * fundamentalSymmetry) := by
            noncomm_ring
      _ = fMinus * (fundamentalSymmetry * (X * fundamentalSymmetry)) * fMinus := by
        rw [hJfP]
  have hKreinQPlus :
      kreinAction (qgtPlus fPlus A C) = qgtMinus fPlus (kreinAction C) (kreinAction A) := by
    unfold qgtPlus qgtMinus
    rw [hKreinMul, hKreinCP, hKreinCM]
  have hKreinQMinus :
      kreinAction (qgtMinus fPlus A C) = qgtPlus fPlus (kreinAction C) (kreinAction A) := by
    unfold qgtPlus qgtMinus
    rw [hKreinMul, hKreinCM, hKreinCP]
  have hKreinV :
      kreinAction (genV fPlus A C) = genV fPlus (kreinAction C) (kreinAction A) := by
    change kreinAction (qgtPlus fPlus A C + qgtMinus fPlus A C) =
      qgtPlus fPlus (kreinAction C) (kreinAction A) +
        qgtMinus fPlus (kreinAction C) (kreinAction A)
    rw [map_add, hKreinQPlus, hKreinQMinus, add_comm]
  have hPcolim : twoSheetColimitEnd plusStage * twoSheetColimitEnd plusStage =
      twoSheetColimitEnd plusStage := twoSheetColimit_plus_idempotent
  exact ⟨hComp,
    even_idempotencyDefect_sub fPlus X fPlus_idempotent,
    hKrein11,
    hKreinQPlus,
    hKreinV,
    hPcolim,
    even_idempotencyDefect_sub (twoSheetColimitEnd plusStage) X_colim hPcolim,
    (peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills
      hPcolim A_colim C_colim X_colim X_colim).2.2.2.2.2.2.2.2.2.1⟩

end InfoGeometry.Categorical.TwoSheetKreinStageSystem
