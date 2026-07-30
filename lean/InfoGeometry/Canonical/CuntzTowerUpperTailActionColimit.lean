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

abbrev upperStageTopologicalColimit (m : ℕ) : TopCat :=
  topologicalDirectColimit (upperStageTopologicalDiagram Stage T m)

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

def upperStageTopologicalInjection (m : ℕ) (j : UpperNatIndex m) :
    (upperStageTopologicalDiagram Stage T m).obj j ⟶
      upperStageTopologicalColimit Stage T m :=
  topologicalDirectInjection (upperStageTopologicalDiagram Stage T m) j

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

end InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
