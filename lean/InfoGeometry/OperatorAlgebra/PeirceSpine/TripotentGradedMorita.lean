/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentMoritaPairings
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Inner-graded Morita equivalence for the full real endomorphism algebra.
The category is encoded by the untwisted C₂ action. Its actual module grading
is Γ_M = Γ_V • J_M, not the A-linear involution J_M alone.
`actionOfGrading` and `grading_reconstruct` recover arbitrary inner-semilinear
involutions; `morphism_even_iff` identifies exactly the even module maps.
The target is the category of real vector spaces with involution.
-/

noncomputable section
open CategoryTheory
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
open InnerGradedMorita

variable {V : Type} [AddCommGroup V] [Module ℝ V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Full operator-algebra Morita equivalence obtained from an arbitrary finite basis. -/
def endomorphismMorita (b : Module.Basis ι ℝ V) (i : ι) :
    MoritaEquivalence ℝ (Module.End ℝ V) ℝ :=
  (MoritaEquivalence.ofAlgEquiv (LinearMap.toMatrixAlgEquiv b)).trans ℝ
    ((moritaEquivalenceMatrix ℝ ℝ i).symm ℝ)

/-- Both functors, natural unit/counit and triangle laws are constructed by the
native action lift of the actual matrix Morita equivalence. -/
def tripotentGradedMorita (b : Module.Basis ι ℝ V) (i : ι) :
    Action (ModuleCat (Module.End ℝ V)) C2 ≌ Action (ModuleCat ℝ) C2 :=
  gradedEquivalence (endomorphismMorita b i).eqv

theorem reflection_mul_self {T : Module.End ℝ V} (hT : T * T * T = T) :
    moduleReflection T * moduleReflection T = 1 := by
  ext v
  exact moduleReflection_apply_apply hT v

theorem operatorModule_grading_sq {T : Module.End ℝ V} (hT : T * T * T = T)
    (X : Action (ModuleCat (Module.End ℝ V)) C2) (x : X.V) :
    grading (moduleReflection T) X (grading (moduleReflection T) X x) = x :=
  grading_sq _ (reflection_mul_self hT) X x

theorem operatorModule_grading_action {T : Module.End ℝ V} (hT : T * T * T = T)
    (X : Action (ModuleCat (Module.End ℝ V)) C2) (a : Module.End ℝ V) (x : X.V) :
    grading (moduleReflection T) X (a • x) =
      gradedHomParity T T a • grading (moduleReflection T) X x := by
  change grading (moduleReflection T) X (a • x) =
    (moduleReflection T * a * moduleReflection T) • grading (moduleReflection T) X x
  exact grading_smul _ (reflection_mul_self hT) X a x

theorem operatorModule_even_iff {T : Module.End ℝ V} (hT : T * T * T = T)
    {X Y : Action (ModuleCat (Module.End ℝ V)) C2} (f : X.V ⟶ Y.V) :
    (∀ x, f (grading (moduleReflection T) X x) = grading (moduleReflection T) Y (f x)) ↔
      ∀ k, X.ρ k ≫ f = f ≫ Y.ρ k :=
  morphism_even_iff _ (reflection_mul_self hT) f

theorem tripotent_unit_even (b : Module.Basis ι ℝ V) (i : ι) (T : Module.End ℝ V)
    (X : Action (ModuleCat (Module.End ℝ V)) C2) (x : X.V) :
    ((tripotentGradedMorita b i).unitIso.hom.app X).hom (grading (moduleReflection T) X x) =
      grading (moduleReflection T) _ (((tripotentGradedMorita b i).unitIso.hom.app X).hom x) :=
  unit_even _ _ X x

theorem tripotent_counit_even (b : Module.Basis ι ℝ V) (i : ι)
    (Y : Action (ModuleCat ℝ) C2)
    (y : ((tripotentGradedMorita b i).functor.obj ((tripotentGradedMorita b i).inverse.obj Y)).V) :
    ((tripotentGradedMorita b i).counitIso.hom.app Y).hom (grading (1 : ℝ) _ y) =
      grading (1 : ℝ) Y (((tripotentGradedMorita b i).counitIso.hom.app Y).hom y) :=
  counit_even _ _ Y y

/-- The concrete forward Morita functor preserves even morphisms in the
`C₂`-action categories. -/
theorem tripotent_functor_preserves_even (b : Module.Basis ι ℝ V) (i : ι)
    {X Y : Action (ModuleCat (Module.End ℝ V)) C2} (f : X ⟶ Y)
    (x : ((tripotentGradedMorita b i).functor.obj X).V) :
    ((tripotentGradedMorita b i).functor.map f).hom
        (grading (1 : ℝ) ((tripotentGradedMorita b i).functor.obj X) x) =
      grading (1 : ℝ) ((tripotentGradedMorita b i).functor.obj Y)
        (((tripotentGradedMorita b i).functor.map f).hom x) :=
  functor_even (endomorphismMorita b i).eqv (1 : ℝ) f x

/-- The concrete inverse Morita functor preserves even morphisms for the
tripotent-induced inner grading on its operator-module values. -/
theorem tripotent_inverse_preserves_even (b : Module.Basis ι ℝ V) (i : ι)
    {T : Module.End ℝ V} (hT : T * T * T = T)
    {X Y : Action (ModuleCat ℝ) C2} (f : X ⟶ Y)
    (x : ((tripotentGradedMorita b i).inverse.obj X).V) :
    ((tripotentGradedMorita b i).inverse.map f).hom
        (grading (moduleReflection T) ((tripotentGradedMorita b i).inverse.obj X) x) =
      grading (moduleReflection T) ((tripotentGradedMorita b i).inverse.obj Y)
        (((tripotentGradedMorita b i).inverse.map f).hom x) :=
  inverse_even (endomorphismMorita b i).eqv (moduleReflection T) f x

theorem tripotent_functor_triangle (b : Module.Basis ι ℝ V) (i : ι)
    (X : Action (ModuleCat (Module.End ℝ V)) C2) :
    (tripotentGradedMorita b i).functor.map ((tripotentGradedMorita b i).unitIso.hom.app X) ≫
      (tripotentGradedMorita b i).counitIso.hom.app ((tripotentGradedMorita b i).functor.obj X) =
        𝟙 ((tripotentGradedMorita b i).functor.obj X) :=
  (tripotentGradedMorita b i).functor_unit_comp X

theorem tripotent_inverse_triangle (b : Module.Basis ι ℝ V) (i : ι)
    (Y : Action (ModuleCat ℝ) C2) :
    (tripotentGradedMorita b i).unitIso.hom.app ((tripotentGradedMorita b i).inverse.obj Y) ≫
      (tripotentGradedMorita b i).inverse.map ((tripotentGradedMorita b i).counitIso.hom.app Y) =
        𝟙 ((tripotentGradedMorita b i).inverse.obj Y) :=
  (tripotentGradedMorita b i).unit_inverse_comp Y

/-- The inverse functor grading is the full matrix action of the source
reflection on the pointwise target involution. No diagonalization is used. -/
theorem tripotent_inverse_grading_apply (b : Module.Basis ι ℝ V) (i : ι)
    (T : Module.End ℝ V) (Y : Action (ModuleCat ℝ) C2)
    (y : ((tripotentGradedMorita b i).inverse.obj Y).V) (j : ι) :
    grading (moduleReflection T) ((tripotentGradedMorita b i).inverse.obj Y) y j =
      ∑ k, (LinearMap.toMatrix b b (moduleReflection T)) j k • involution Y (y k) := by
  rfl

end InfoGeometry.OperatorAlgebra.PeirceSpine
