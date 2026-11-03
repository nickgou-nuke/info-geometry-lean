/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentGradedMorita
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentMoritaForwardFunctor
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentCornerEndEquivalence

/-!
# D₃₉: Graded tripotent Morita synthesis

This theorem packages the repository's finite-dimensional, basis-indexed Morita
equivalence. The basis-selected rank-one idempotent also has a proved corner
comparison: the opposite of its corner is the endomorphism ring of its left
ideal, by right multiplication. A tripotent alone in an arbitrary ring is not
asserted to give a full-corner Morita equivalence. The graded unit and counit
remain the existing action-category isomorphisms; they are not inferred from
an algebra involution on the corner.
-/

noncomputable section
open CategoryTheory
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
open InnerGradedMorita

variable {V : Type} [AddCommGroup V] [Module ℝ V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The complete graded Morita checklist for the actual finite-basis
endomorphism-algebra equivalence: the quotient-to-corner comparison, even
morphism preservation in both directions, even unit and counit, and both
equivalence triangles. -/
theorem tripotent_graded_morita_D39
    [Module.Finite ℝ V]
    (b : Module.Basis ι ℝ V) (i : ι) (T : Module.End ℝ V)
    (hT : T * T * T = T) :
    Nonempty (MoritaEquivalence ℝ (Module.End ℝ V) ℝ) ∧
    Nonempty (gradedForwardBalancedTensorFunctor (V := V) ≅
      (forwardCornerFunctor (V := V) b i).mapAction InnerGradedMorita.C2) ∧
    (∀ X Y : Module.End ℝ V,
      parityConj (InfoGeometry.Physics.Algebra.projZero T) (X * Y) =
        parityConj (InfoGeometry.Physics.Algebra.projZero T) X *
          parityConj (InfoGeometry.Physics.Algebra.projZero T) Y) ∧
    (∀ (X : Action (ModuleCat (Module.End ℝ V)) InnerGradedMorita.C2)
        (a : Module.End ℝ V) (x : X.V),
      grading (moduleReflection T) X (a • x) =
        gradedHomParity T T a • grading (moduleReflection T) X x) ∧
    (∀ (a f b : Module.End ℝ V),
      gradedHomParity T T (a.comp (f.comp b)) =
        (gradedHomParity T T a).comp
          ((gradedHomParity T T f).comp (gradedHomParity T T b))) ∧
    (∀ (X : Action (ModuleCat (Module.End ℝ V)) InnerGradedMorita.C2) (x : X.V),
      ((tripotentGradedMorita b i).unitIso.hom.app X).hom
          (grading (moduleReflection T) X x) =
        grading (moduleReflection T) _
          (((tripotentGradedMorita b i).unitIso.hom.app X).hom x)) ∧
    (∀ (Y : Action (ModuleCat ℝ) InnerGradedMorita.C2)
        (y : ((tripotentGradedMorita b i).functor.obj
          ((tripotentGradedMorita b i).inverse.obj Y)).V),
      ((tripotentGradedMorita b i).counitIso.hom.app Y).hom
          (grading (1 : ℝ) _ y) =
        grading (1 : ℝ) Y
          (((tripotentGradedMorita b i).counitIso.hom.app Y).hom y)) ∧
    (∀ {X Y : Action (ModuleCat (Module.End ℝ V)) InnerGradedMorita.C2}
        (f : X ⟶ Y) x,
      ((tripotentGradedMorita b i).functor.map f).hom
          (grading (1 : ℝ) ((tripotentGradedMorita b i).functor.obj X) x) =
        grading (1 : ℝ) ((tripotentGradedMorita b i).functor.obj Y)
          (((tripotentGradedMorita b i).functor.map f).hom x)) ∧
    (∀ {X Y : Action (ModuleCat ℝ) InnerGradedMorita.C2}
        (f : X ⟶ Y)
        (x : ((tripotentGradedMorita b i).inverse.obj X).V),
      ((tripotentGradedMorita b i).inverse.map f).hom
          (grading (moduleReflection T) ((tripotentGradedMorita b i).inverse.obj X) x) =
        grading (moduleReflection T) ((tripotentGradedMorita b i).inverse.obj Y)
          (((tripotentGradedMorita b i).inverse.map f).hom x)) ∧
    (∀ X,
      (tripotentGradedMorita b i).functor.map
          ((tripotentGradedMorita b i).unitIso.hom.app X) ≫
        (tripotentGradedMorita b i).counitIso.hom.app
          ((tripotentGradedMorita b i).functor.obj X) =
        𝟙 ((tripotentGradedMorita b i).functor.obj X)) ∧
    (∀ Y,
      (tripotentGradedMorita b i).unitIso.hom.app
          ((tripotentGradedMorita b i).inverse.obj Y) ≫
        (tripotentGradedMorita b i).inverse.map
          ((tripotentGradedMorita b i).counitIso.hom.app Y) =
        𝟙 ((tripotentGradedMorita b i).inverse.obj Y)) ∧
    Nonempty ((idempotentCorner (basisCornerIdem b i)
      (basisCornerIdem_idem b i))ᵐᵒᵖ ≃+*
        Module.End (Module.End ℝ V)
          (idempotentLeftIdeal (basisCornerIdem b i) (basisCornerIdem_idem b i))) := by
  refine ⟨⟨endomorphismMorita b i⟩,
    ⟨gradedForwardBalancedTensorCornerNatIso (V := V) b i⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y
    exact (parityConj_involutive_ring_action
      (InfoGeometry.Physics.Algebra.projZero_idempotent hT) X Y).2.1
  · intro X a x
    exact operatorModule_grading_action hT X a x
  · intro a f b'
    exact gradedHomParity_bimodule hT hT a f b'
  · intro X x
    exact tripotent_unit_even b i T X x
  · intro Y y
    exact tripotent_counit_even b i Y y
  · intro X Y f x
    exact tripotent_functor_preserves_even b i f x
  · intro X Y f x
    exact tripotent_inverse_preserves_even b i hT f x
  · intro X
    exact tripotent_functor_triangle b i X
  · intro Y
    exact tripotent_inverse_triangle b i Y
  · exact ⟨idempotentCornerEndEquiv (basisCornerIdem b i)
      (basisCornerIdem_idem b i)⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
end
