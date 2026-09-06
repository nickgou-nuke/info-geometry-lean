import InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit

/-!
# Cuntz corner relations on the upper-tail TopCat colimit

The upper-tail action maps are already descended by `colim.map`.  This owner
adds the noncommutative corner readout: the composite of left multiplication
by an old generator and right multiplication by a later adjoint generator is
identified exactly on every canonical stage injection.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzTowerUpperTailActionRelationsTopological

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def upperGeneratorCornerColimitMap
    (m : ℕ) (i k : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  upperLeftGeneratorActionColimitMap Stage T m i ≫
    upperRightAdjointGeneratorActionColimitMap Stage T m k

def upperLeftAdjointGeneratorActionNatTrans
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalDiagram Stage T m ⟶
      upperStageTopologicalDiagram Stage T m where
  app j := show TopCat.of (Stage j.1) ⟶ TopCat.of (Stage j.1) from
    TopCat.ofHom
      (ContinuousMap.mulLeft
        (star ((T.family j.1).S (Fin.castLE j.2 i))) :
        ContinuousMap (Stage j.1) (Stage j.1))
  naturality := by
    intro j k f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change Stage j.1 at a
    have hgen :
        T.map (leOfHom f)
            (star ((T.family j.1).S (Fin.castLE j.2 i))) =
          star ((T.family k.1).S (Fin.castLE k.2 i)) := by
      rw [CuntzStarTower.map_generator_star (Stage := Stage) T
        (leOfHom f) (Fin.castLE j.2 i)]
      congr 1
    calc
      star ((T.family k.1).S (Fin.castLE k.2 i)) * T.map (leOfHom f) a =
          T.map (leOfHom f) (star ((T.family j.1).S (Fin.castLE j.2 i))) *
            T.map (leOfHom f) a := by rw [hgen]
      _ = T.map (leOfHom f)
          (star ((T.family j.1).S (Fin.castLE j.2 i)) * a) := by
            rw [map_mul]

@[simp] theorem upperLeftAdjointGeneratorActionNatTrans_apply
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (a : Stage j.1) :
    (upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j a =
      star ((T.family j.1).S (Fin.castLE j.2 i)) * a := rfl

noncomputable def upperLeftAdjointGeneratorActionColimitMap
    (m : ℕ) (i : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  colim.map (upperLeftAdjointGeneratorActionNatTrans Stage T m i)

theorem upperLeftAdjointGeneratorActionColimitMap_stage
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (a : Stage j.1) :
    upperLeftAdjointGeneratorActionColimitMap Stage T m i
        (upperStageTopologicalInjection Stage T m j a) =
      upperStageTopologicalInjection Stage T m j
        (star ((T.family j.1).S (Fin.castLE j.2 i)) * a) := by
  have h := colimit.ι_map
    (upperLeftAdjointGeneratorActionNatTrans Stage T m i) j
  exact congrArg (fun f => f a) h

def upperCuntzInitialRelationColimitMap
  (m : ℕ) (i k : Fin m) :
    upperStageTopologicalColimit Stage T m ⟶
      upperStageTopologicalColimit Stage T m :=
  upperLeftGeneratorActionColimitMap Stage T m k ≫
    upperLeftAdjointGeneratorActionColimitMap Stage T m i

theorem upperCuntzInitialRelationColimitMap_stage
    (m : ℕ) (i k : Fin m) (j : UpperNatIndex m) (a : Stage j.1) :
    upperCuntzInitialRelationColimitMap Stage T m i k
        (upperStageTopologicalInjection Stage T m j a) =
      if i = k then
        upperStageTopologicalInjection Stage T m j a
      else
        upperStageTopologicalInjection Stage T m j (0 : Stage j.1) := by
  have hleft := upperLeftGeneratorActionColimitMap_stage
    Stage T m k j
  have hadj :
      upperStageTopologicalInjection Stage T m j ≫
          upperLeftAdjointGeneratorActionColimitMap Stage T m i =
        (upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
          upperStageTopologicalInjection Stage T m j := by
    exact colimit.ι_map
      (upperLeftAdjointGeneratorActionNatTrans Stage T m i) j
  have hcomp :
      upperStageTopologicalInjection Stage T m j ≫
          upperCuntzInitialRelationColimitMap Stage T m i k =
          (upperLeftGeneratorActionNatTrans Stage T m k).app j ≫
          (upperLeftAdjointGeneratorActionNatTrans Stage T m i).app j ≫
            upperStageTopologicalInjection Stage T m j := by
    dsimp [upperCuntzInitialRelationColimitMap]
    rw [← Category.assoc, hleft, Category.assoc, hadj, ← Category.assoc]
  have heval := congrArg (fun f => f a) hcomp
  by_cases hik : i = k
  · subst k
    have hinner :
        star ((T.family j.1).S (Fin.castLE j.2 i)) *
            ((T.family j.1).S (Fin.castLE j.2 i) * a) = a := by
      rw [← mul_assoc, isometry_relation (F := T.family j.1) _]
      simp
    simpa [upperLeftAdjointGeneratorActionNatTrans,
      upperLeftGeneratorActionNatTrans, hinner] using heval
  · have hcast : Fin.castLE j.2 i ≠ Fin.castLE j.2 k := by
      intro h
      exact hik ((Fin.castLE_injective j.2) h)
    have hinner :
        star ((T.family j.1).S (Fin.castLE j.2 i)) *
            ((T.family j.1).S (Fin.castLE j.2 k) * a) = 0 := by
      rw [← mul_assoc, orthogonal_relation (F := T.family j.1) hcast]
      simp
    simpa [upperLeftAdjointGeneratorActionNatTrans,
      upperLeftGeneratorActionNatTrans, hinner, hik] using heval

theorem upperCuntzInitialRelationColimitMap_eq_id
    (m : ℕ) (i : Fin m) :
    upperCuntzInitialRelationColimitMap Stage T m i i =
      𝟙 (upperStageTopologicalColimit Stage T m) := by
  apply colimit.hom_ext
  intro j
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  simpa using upperCuntzInitialRelationColimitMap_stage
    Stage T m i i j a

theorem upperGeneratorCornerColimitMap_stage
    (m : ℕ) (i k : Fin m) (j : UpperNatIndex m) (a : Stage j.1) :
    upperGeneratorCornerColimitMap Stage T m i k
        (upperStageTopologicalInjection Stage T m j a) =
      upperStageTopologicalInjection Stage T m j
        ((T.family j.1).S (Fin.castLE j.2 i) * a *
          star ((T.family j.1).S (Fin.castLE j.2 k))) := by
  have hleft := upperLeftGeneratorActionColimitMap_stage
    Stage T m i j
  have hright := upperRightAdjointGeneratorActionColimitMap_stage
    Stage T m k j
  have hcomp :
      upperStageTopologicalInjection Stage T m j ≫
          upperGeneratorCornerColimitMap Stage T m i k =
        (upperLeftGeneratorActionNatTrans Stage T m i).app j ≫
          (upperRightAdjointGeneratorActionNatTrans Stage T m k).app j ≫
            upperStageTopologicalInjection Stage T m j := by
    dsimp [upperGeneratorCornerColimitMap]
    rw [← Category.assoc, hleft, Category.assoc, hright,
      ← Category.assoc]
  have heval := congrArg (fun f => f a) hcomp
  simpa [upperLeftGeneratorActionNatTrans,
    upperRightAdjointGeneratorActionNatTrans] using heval

end InfoGeometry.Canonical.CuntzTowerUpperTailActionRelationsTopological
