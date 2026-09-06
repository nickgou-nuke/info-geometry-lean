import InfoGeometry.Canonical.CuntzTowerGeneratorActionTopological
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Upper-tail Cuntz actions on a topological colimit

An old generator is only defined canonically on later stages of a Cuntz tower.
This file restricts the stage diagram to the upper tail, packages left and
right generator actions as natural transformations, and descends them with
`TopCat`'s `colim.map`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerGeneratorActionTopological
open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

abbrev UpperNatIndex (m : ℕ) := {n : ℕ // m ≤ n}

def upperStageTopologicalDiagram (m : ℕ) :
    UpperNatIndex m ⥤ TopCat where
  obj j := TopCat.of (Stage j.1)
  map f := towerTransitionTopCatHom Stage T (leOfHom f)
  map_id j := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    simp [towerTransitionTopCatHom, T.map_id]
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change T.map (le_trans (leOfHom f) (leOfHom g)) a =
      T.map (leOfHom g) (T.map (leOfHom f) a)
    exact congrArg (fun e => e a)
      (T.map_comp (leOfHom f) (leOfHom g)).symm

def upperLeftGeneratorActionNatTrans
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalDiagram Stage T m ⟶
      upperStageTopologicalDiagram Stage T m where
  app j := TopCat.ofHom
    ((T.family j.1).leftGeneratorAction (Fin.castLE j.2 i))
  naturality := by
    intro j k f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    have h := tower_left_generator_action_natural Stage T (leOfHom f)
      (Fin.castLE j.2 i)
    exact congrArg (fun e => e a) h

def upperRightAdjointGeneratorActionNatTrans
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalDiagram Stage T m ⟶
      upperStageTopologicalDiagram Stage T m where
  app j := TopCat.ofHom
    ((T.family j.1).rightAdjointGeneratorAction (Fin.castLE j.2 i))
  naturality := by
    intro j k f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    have h := tower_right_adjoint_generator_action_natural Stage T (leOfHom f)
      (Fin.castLE j.2 i)
    exact congrArg (fun e => e a) h.symm

def upperLeftAdjointGeneratorActionNatTrans
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalDiagram Stage T m ⟶
      upperStageTopologicalDiagram Stage T m where
  app j := TopCat.ofHom
    ((T.family j.1).leftAdjointGeneratorAction (Fin.castLE j.2 i))
  naturality := by
    intro j k f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change star ((T.family k.1).S (Fin.castLE k.2 i)) *
        T.map (leOfHom f) (show Stage j.1 from a) =
      T.map (leOfHom f)
        (star ((T.family j.1).S (Fin.castLE j.2 i)) *
          (show Stage j.1 from a))
    rw [map_mul, T.map_generator_star]
    simp

abbrev upperStageTopologicalColimit (m : ℕ) : TopCat :=
  colimit (upperStageTopologicalDiagram Stage T m)

noncomputable def upperLeftGeneratorActionColimitMap
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  colim.map (upperLeftGeneratorActionNatTrans Stage T m i)

noncomputable def upperRightAdjointGeneratorActionColimitMap
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  colim.map (upperRightAdjointGeneratorActionNatTrans Stage T m i)

noncomputable def upperLeftAdjointGeneratorActionColimitMap
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  colim.map (upperLeftAdjointGeneratorActionNatTrans Stage T m i)

noncomputable def upperGeneratorProjectionColimitMap
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  upperLeftAdjointGeneratorActionColimitMap Stage T m i ≫
    upperLeftGeneratorActionColimitMap Stage T m i

noncomputable def upperGeneratorCornerColimitMap
    (m : ℕ) (i j : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  upperLeftGeneratorActionColimitMap Stage T m i ≫
    upperRightAdjointGeneratorActionColimitMap Stage T m j

def upperStageTopologicalInjection (m : ℕ) (j : UpperNatIndex m) :
    (upperStageTopologicalDiagram Stage T m).obj j ⟶
      upperStageTopologicalColimit Stage T m :=
  colimit.ι (upperStageTopologicalDiagram Stage T m) j

theorem upperLeftGeneratorActionColimitMap_stage
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    upperStageTopologicalInjection Stage T m j ≫
        upperLeftGeneratorActionColimitMap Stage T m i =
      (upperLeftGeneratorActionNatTrans Stage T m i).app j ≫
        upperStageTopologicalInjection Stage T m j := by
  exact colimit.ι_map (upperLeftGeneratorActionNatTrans Stage T m i) j

theorem upperRightAdjointGeneratorActionColimitMap_stage
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    upperStageTopologicalInjection Stage T m j ≫
        upperRightAdjointGeneratorActionColimitMap Stage T m i =
      (upperRightAdjointGeneratorActionNatTrans Stage T m i).app j ≫
        upperStageTopologicalInjection Stage T m j := by
  exact colimit.ι_map
    (upperRightAdjointGeneratorActionNatTrans Stage T m i) j

theorem upperLeftAdjointGeneratorActionColimitMap_stage
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    upperStageTopologicalInjection Stage T m j ≫
        upperLeftAdjointGeneratorActionColimitMap Stage T m i =
      (upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
        upperStageTopologicalInjection Stage T m j := by
  exact colimit.ι_map
    (upperLeftAdjointGeneratorActionNatTrans Stage T m i) j

theorem upperGeneratorProjectionColimitMap_stage
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    upperStageTopologicalInjection Stage T m j ≫
        upperGeneratorProjectionColimitMap Stage T m i =
      ((upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
        (upperLeftGeneratorActionNatTrans Stage T m i).app j) ≫
          upperStageTopologicalInjection Stage T m j := by
  rw [upperGeneratorProjectionColimitMap, ← Category.assoc,
    upperLeftAdjointGeneratorActionColimitMap_stage,
    Category.assoc, upperLeftGeneratorActionColimitMap_stage,
    Category.assoc]

theorem upperGeneratorProjectionColimitMap_stage_apply
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (x : Stage j.1) :
    (upperStageTopologicalInjection Stage T m j ≫
        upperGeneratorProjectionColimitMap Stage T m i) x =
      upperStageTopologicalInjection Stage T m j
        ((T.family j.1).S (Fin.castLE j.2 i) *
          (star ((T.family j.1).S (Fin.castLE j.2 i)) * x)) := by
  rw [upperGeneratorProjectionColimitMap_stage]
  rfl

theorem upperGeneratorProjectionColimitMap_idempotent
    (m : ℕ) (i : Fin m) :
    upperGeneratorProjectionColimitMap Stage T m i ≫
        upperGeneratorProjectionColimitMap Stage T m i =
      upperGeneratorProjectionColimitMap Stage T m i := by
  apply colimit.hom_ext
  intro j
  have hstage :=
    leftAdjointGeneratorActionTopCatHom_comp_leftGeneratorActionTopCatHom_idempotent
      (T.family j.1) (Fin.castLE j.2 i)
  calc
    upperStageTopologicalInjection Stage T m j ≫
        (upperGeneratorProjectionColimitMap Stage T m i ≫
          upperGeneratorProjectionColimitMap Stage T m i) =
      (upperStageTopologicalInjection Stage T m j ≫
        upperGeneratorProjectionColimitMap Stage T m i) ≫
          upperGeneratorProjectionColimitMap Stage T m i := by
      rw [Category.assoc]
    _ = (((upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
          (upperLeftGeneratorActionNatTrans Stage T m i).app j) ≫
        upperStageTopologicalInjection Stage T m j) ≫
          upperGeneratorProjectionColimitMap Stage T m i := by
      rw [upperGeneratorProjectionColimitMap_stage]
    _ = ((upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
          (upperLeftGeneratorActionNatTrans Stage T m i).app j) ≫
        (upperStageTopologicalInjection Stage T m j ≫
          upperGeneratorProjectionColimitMap Stage T m i) := by
      rw [Category.assoc]
    _ = ((upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
          (upperLeftGeneratorActionNatTrans Stage T m i).app j) ≫
        (((upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
          (upperLeftGeneratorActionNatTrans Stage T m i).app j) ≫
            upperStageTopologicalInjection Stage T m j) := by
      rw [upperGeneratorProjectionColimitMap_stage]
    _ = ((upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
          (upperLeftGeneratorActionNatTrans Stage T m i).app j) ≫
        upperStageTopologicalInjection Stage T m j := by
      rw [show
        (upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
            (upperLeftGeneratorActionNatTrans Stage T m i).app j =
          (T.family j.1).leftAdjointGeneratorActionTopCatHom
              (Fin.castLE j.2 i) ≫
            (T.family j.1).leftGeneratorActionTopCatHom
              (Fin.castLE j.2 i) by rfl]
      have h := congrArg
        (fun q => q ≫ upperStageTopologicalInjection Stage T m j) hstage
      simpa only [Category.assoc] using h
    _ = upperStageTopologicalInjection Stage T m j ≫
        upperGeneratorProjectionColimitMap Stage T m i := by
      exact (upperGeneratorProjectionColimitMap_stage Stage T m i j).symm

theorem upperGeneratorCornerColimitMap_stage
    (m : ℕ) (i j : Fin m) (k : UpperNatIndex m) :
    upperStageTopologicalInjection Stage T m k ≫
        upperGeneratorCornerColimitMap Stage T m i j =
      (upperLeftGeneratorActionNatTrans Stage T m i).app k ≫
      (upperRightAdjointGeneratorActionNatTrans Stage T m j).app k ≫
          upperStageTopologicalInjection Stage T m k := by
  rw [upperGeneratorCornerColimitMap, ← Category.assoc,
    upperLeftGeneratorActionColimitMap_stage,
    Category.assoc, upperRightAdjointGeneratorActionColimitMap_stage]

theorem upperGeneratorActionColimitMap_comm_of
    (m : ℕ) (i j' : Fin m) :
    upperLeftGeneratorActionColimitMap Stage T m i ≫
        upperRightAdjointGeneratorActionColimitMap Stage T m j' =
      upperRightAdjointGeneratorActionColimitMap Stage T m j' ≫
        upperLeftGeneratorActionColimitMap Stage T m i := by
  apply colimit.hom_ext
  intro j
  change
    (upperStageTopologicalInjection Stage T m j ≫
        upperLeftGeneratorActionColimitMap Stage T m i) ≫
        upperRightAdjointGeneratorActionColimitMap Stage T m j' =
      (upperStageTopologicalInjection Stage T m j ≫
        upperRightAdjointGeneratorActionColimitMap Stage T m j') ≫
        upperLeftGeneratorActionColimitMap Stage T m i
  have hstage :
      (upperLeftGeneratorActionNatTrans Stage T m i).app j ≫
          (upperRightAdjointGeneratorActionNatTrans Stage T m j').app j =
        (upperRightAdjointGeneratorActionNatTrans Stage T m j').app j ≫
          (upperLeftGeneratorActionNatTrans Stage T m i).app j := by
    apply TopCat.hom_ext
    simpa [upperLeftGeneratorActionNatTrans,
      upperRightAdjointGeneratorActionNatTrans, TopCat.ofHom] using
      (leftGeneratorAction_comp_rightAdjointGeneratorAction
        (T.family j.1) (Fin.castLE j.2 i) (Fin.castLE j.2 j')).symm
  calc
    (upperStageTopologicalInjection Stage T m j ≫
        upperLeftGeneratorActionColimitMap Stage T m i) ≫
        upperRightAdjointGeneratorActionColimitMap Stage T m j' =
      (upperLeftGeneratorActionNatTrans Stage T m i).app j ≫
        (upperStageTopologicalInjection Stage T m j ≫
          upperRightAdjointGeneratorActionColimitMap Stage T m j') := by
      rw [upperLeftGeneratorActionColimitMap_stage, Category.assoc]
    _ = (upperLeftGeneratorActionNatTrans Stage T m i).app j ≫
        ((upperRightAdjointGeneratorActionNatTrans Stage T m j').app j ≫
          upperStageTopologicalInjection Stage T m j) := by
      rw [upperRightAdjointGeneratorActionColimitMap_stage]
    _ = (upperRightAdjointGeneratorActionNatTrans Stage T m j').app j ≫
        ((upperLeftGeneratorActionNatTrans Stage T m i).app j ≫
          upperStageTopologicalInjection Stage T m j) := by
      rw [← Category.assoc, hstage, Category.assoc]
    _ = (upperStageTopologicalInjection Stage T m j ≫
        upperRightAdjointGeneratorActionColimitMap Stage T m j') ≫
        upperLeftGeneratorActionColimitMap Stage T m i := by
      rw [upperRightAdjointGeneratorActionColimitMap_stage,
        Category.assoc, upperLeftGeneratorActionColimitMap_stage]

theorem upperGeneratorActionColimitMap_comm
    (m : ℕ) (i : Fin m) :
    upperLeftGeneratorActionColimitMap Stage T m i ≫
        upperRightAdjointGeneratorActionColimitMap Stage T m i =
      upperRightAdjointGeneratorActionColimitMap Stage T m i ≫
        upperLeftGeneratorActionColimitMap Stage T m i :=
  upperGeneratorActionColimitMap_comm_of Stage T m i i

end InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
