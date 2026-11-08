/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentMoritaForwardBimodule
import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Action.Basic

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {V : Type} [AddCommGroup V] [Module ℝ V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem moduleCatScalarComm (M : ModuleCat (Module.End ℝ V)) :
    SMulCommClass ℝ (Module.End ℝ V) M :=
  SMulCommClass.symm (M := Module.End ℝ V) (N := ℝ) M

/-- Tensoring with the right operator-module `V*`, represented by the explicit
balanced-tensor quotient, defines a functor on operator modules. -/
def forwardBalancedTensorFunctor :
    ModuleCat (Module.End ℝ V) ⥤ ModuleCat ℝ where
  obj M := by
    letI : Module ℝ M := ModuleCat.moduleOfAlgebraModule M
    letI : IsScalarTower ℝ (Module.End ℝ V) M :=
      ModuleCat.isScalarTower_of_algebra_moduleCat M
    letI : SMulCommClass ℝ (Module.End ℝ V) M := moduleCatScalarComm M
    exact ModuleCat.of ℝ (forwardMoritaTensor (V := V) M)
  map {M N} f := by
    letI : Module ℝ M := ModuleCat.moduleOfAlgebraModule M
    letI : IsScalarTower ℝ (Module.End ℝ V) M :=
      ModuleCat.isScalarTower_of_algebra_moduleCat M
    letI : SMulCommClass ℝ (Module.End ℝ V) M := moduleCatScalarComm M
    letI : Module ℝ N := ModuleCat.moduleOfAlgebraModule N
    letI : IsScalarTower ℝ (Module.End ℝ V) N :=
      ModuleCat.isScalarTower_of_algebra_moduleCat N
    letI : SMulCommClass ℝ (Module.End ℝ V) N := moduleCatScalarComm N
    exact ModuleCat.ofHom <| forwardMoritaTensorMap (V := V) (M := M) (N := N)
      (f.hom.restrictScalars ℝ) (by intro a m; exact f.hom.map_smul a m)
  map_id M := by
    letI : Module ℝ M := ModuleCat.moduleOfAlgebraModule M
    letI : IsScalarTower ℝ (Module.End ℝ V) M :=
      ModuleCat.isScalarTower_of_algebra_moduleCat M
    letI : SMulCommClass ℝ (Module.End ℝ V) M := moduleCatScalarComm M
    apply ModuleCat.hom_ext
    ext q
    simp [forwardMoritaTensorMap]
  map_comp {X Y Z} f g := by
    letI : Module ℝ X := ModuleCat.moduleOfAlgebraModule X
    letI : IsScalarTower ℝ (Module.End ℝ V) X :=
      ModuleCat.isScalarTower_of_algebra_moduleCat X
    letI : SMulCommClass ℝ (Module.End ℝ V) X := moduleCatScalarComm X
    letI : Module ℝ Y := ModuleCat.moduleOfAlgebraModule Y
    letI : IsScalarTower ℝ (Module.End ℝ V) Y :=
      ModuleCat.isScalarTower_of_algebra_moduleCat Y
    letI : SMulCommClass ℝ (Module.End ℝ V) Y := moduleCatScalarComm Y
    letI : Module ℝ Z := ModuleCat.moduleOfAlgebraModule Z
    letI : IsScalarTower ℝ (Module.End ℝ V) Z :=
      ModuleCat.isScalarTower_of_algebra_moduleCat Z
    letI : SMulCommClass ℝ (Module.End ℝ V) Z := moduleCatScalarComm Z
    apply ModuleCat.hom_ext
    ext q
    simp [forwardMoritaTensorMap]

/-- The graded forward tensor construction is induced by functoriality on C₂
actions; morphisms in the action category are exactly the even maps. -/
def gradedForwardBalancedTensorFunctor :
    Action (ModuleCat (Module.End ℝ V)) InnerGradedMorita.C2 ⥤
      Action (ModuleCat ℝ) InnerGradedMorita.C2 :=
  (forwardBalancedTensorFunctor (V := V)).mapAction InnerGradedMorita.C2

/-- The selected corner is functorial under all operator-module maps. -/
def forwardCornerFunctor (b : Module.Basis ι ℝ V) (i : ι) :
    ModuleCat (Module.End ℝ V) ⥤ ModuleCat ℝ where
  obj M := by
    letI : Module ℝ M := ModuleCat.moduleOfAlgebraModule M
    letI : IsScalarTower ℝ (Module.End ℝ V) M :=
      ModuleCat.isScalarTower_of_algebra_moduleCat M
    letI : SMulCommClass ℝ (Module.End ℝ V) M := moduleCatScalarComm M
    exact ModuleCat.of ℝ (basisCorner b i M)
  map {M N} f := by
    letI : Module ℝ M := ModuleCat.moduleOfAlgebraModule M
    letI : IsScalarTower ℝ (Module.End ℝ V) M :=
      ModuleCat.isScalarTower_of_algebra_moduleCat M
    letI : SMulCommClass ℝ (Module.End ℝ V) M := moduleCatScalarComm M
    letI : Module ℝ N := ModuleCat.moduleOfAlgebraModule N
    letI : IsScalarTower ℝ (Module.End ℝ V) N :=
      ModuleCat.isScalarTower_of_algebra_moduleCat N
    letI : SMulCommClass ℝ (Module.End ℝ V) N := moduleCatScalarComm N
    exact ModuleCat.ofHom <| basisCornerMap (V := V) (b := b) (i := i)
      (M := M) (N := N) (f := f.hom.restrictScalars ℝ)
      (hf := by intro a m; exact f.hom.map_smul a m)
  map_id M := by
    letI : Module ℝ M := ModuleCat.moduleOfAlgebraModule M
    letI : IsScalarTower ℝ (Module.End ℝ V) M :=
      ModuleCat.isScalarTower_of_algebra_moduleCat M
    letI : SMulCommClass ℝ (Module.End ℝ V) M := moduleCatScalarComm M
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp {X Y Z} f g := by
    letI : Module ℝ X := ModuleCat.moduleOfAlgebraModule X
    letI : IsScalarTower ℝ (Module.End ℝ V) X :=
      ModuleCat.isScalarTower_of_algebra_moduleCat X
    letI : SMulCommClass ℝ (Module.End ℝ V) X := moduleCatScalarComm X
    letI : Module ℝ Y := ModuleCat.moduleOfAlgebraModule Y
    letI : IsScalarTower ℝ (Module.End ℝ V) Y :=
      ModuleCat.isScalarTower_of_algebra_moduleCat Y
    letI : SMulCommClass ℝ (Module.End ℝ V) Y := moduleCatScalarComm Y
    letI : Module ℝ Z := ModuleCat.moduleOfAlgebraModule Z
    letI : IsScalarTower ℝ (Module.End ℝ V) Z :=
      ModuleCat.isScalarTower_of_algebra_moduleCat Z
    letI : SMulCommClass ℝ (Module.End ℝ V) Z := moduleCatScalarComm Z
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Natural isomorphism from the balanced tensor quotient to the selected
rank-one corner. Naturality is the full quotient-level tensor-map theorem. -/
def forwardBalancedTensorCornerNatIso [Module.Finite ℝ V]
    (b : Module.Basis ι ℝ V) (i : ι) :
    forwardBalancedTensorFunctor (V := V) ≅ forwardCornerFunctor (V := V) b i :=
  NatIso.ofComponents (fun M =>
    (forwardMoritaTensorEquiv (V := V) b i M).toModuleIso) (by
      intro M N f
      letI : Module ℝ M := ModuleCat.moduleOfAlgebraModule M
      letI : IsScalarTower ℝ (Module.End ℝ V) M :=
        ModuleCat.isScalarTower_of_algebra_moduleCat M
      letI : SMulCommClass ℝ (Module.End ℝ V) M := moduleCatScalarComm M
      letI : Module ℝ N := ModuleCat.moduleOfAlgebraModule N
      letI : IsScalarTower ℝ (Module.End ℝ V) N :=
        ModuleCat.isScalarTower_of_algebra_moduleCat N
      letI : SMulCommClass ℝ (Module.End ℝ V) N := moduleCatScalarComm N
      apply ModuleCat.hom_ext
      ext q
      exact (forwardMoritaMap_natural (V := V) (b := b) (i := i)
        (M := M) (N := N) (f := f.hom.restrictScalars ℝ)
        (hf := by intro a m; exact f.hom.map_smul a m) q).symm)

/-- The quotient-to-corner comparison also holds in the categories of C₂-actions,
so it is an isomorphism of inner-graded module functors. -/
def gradedForwardBalancedTensorCornerNatIso
    [Module.Finite ℝ V] (b : Module.Basis ι ℝ V) (i : ι) :
    gradedForwardBalancedTensorFunctor (V := V) ≅
      (forwardCornerFunctor (V := V) b i).mapAction InnerGradedMorita.C2 :=
  Functor.mapActionCongr InnerGradedMorita.C2
    (forwardBalancedTensorCornerNatIso (V := V) b i)

end InfoGeometry.OperatorAlgebra.PeirceSpine
