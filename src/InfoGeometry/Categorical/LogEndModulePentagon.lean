/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.LogEndModuleCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Categorical.LogEndModulePentagon

Mac Lane pentagon for the tensor-stable category of modules equipped with a
distinguished logarithmic endomorphism.

The associator is the ordinary module tensor associator, already proved in
`LogEndModuleCategory` to intertwine the primitive logarithmic endomorphism.
Here the two four-object reassociation composites are proved equal as morphisms
of logarithmic-endomorphism modules.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogEndModulePentagon

open CategoryTheory
open scoped TensorProduct
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule

universe u v

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem logEndModulePentagon_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

section NoncommRing

variable {R : Type u} [Ring R]

/-- Fourfold composition associativity in `LogEndModule R` over any noncommutative `[Ring R]`. -/
theorem ring_comp_fourfold_assoc
    {A B C D E : LogEndModule.{u, v} R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) :
    ((f ≫ g) ≫ h) ≫ k = f ≫ (g ≫ (h ≫ k)) := by
  simp [Category.assoc]

end NoncommRing

variable {𝕜 : Type u} [CommRing 𝕜]

/-- Mac Lane's pentagon identity for the lifted logarithmic associator. -/
theorem pentagon_identity
    (W X Y Z : LogEndModule 𝕜) :
    associatorHom (tensorObj W X) Y Z ≫
        associatorHom W X (tensorObj Y Z) =
      tensorHom (associatorHom W X Y) (𝟙 Z) ≫
        associatorHom W (tensorObj X Y) Z ≫
        tensorHom (𝟙 W) (associatorHom X Y Z) := by
  apply Hom.ext
  apply TensorProduct.ext_fourfold
  intro w x y z
  change (TensorProduct.assoc 𝕜 W.V X.V (Y.V ⊗[𝕜] Z.V))
      ((TensorProduct.assoc 𝕜 (W.V ⊗[𝕜] X.V) Y.V Z.V)
        (w ⊗ₜ[𝕜] x ⊗ₜ[𝕜] y ⊗ₜ[𝕜] z)) =
    (TensorProduct.map (LinearMap.id : Module.End 𝕜 W.V)
        (TensorProduct.assoc 𝕜 X.V Y.V Z.V).toLinearMap)
      ((TensorProduct.assoc 𝕜 W.V (X.V ⊗[𝕜] Y.V) Z.V)
        ((TensorProduct.map (TensorProduct.assoc 𝕜 W.V X.V Y.V).toLinearMap
          (LinearMap.id : Module.End 𝕜 Z.V))
          (w ⊗ₜ[𝕜] x ⊗ₜ[𝕜] y ⊗ₜ[𝕜] z)))
  rw [TensorProduct.assoc_tmul, TensorProduct.assoc_tmul]
  simp only [TensorProduct.map_tmul, TensorProduct.assoc_tmul]
  exact (congrArg (fun t => w ⊗ₜ[𝕜] t)
    (TensorProduct.assoc_tmul (R := 𝕜) x y z)).symm

/-- The same pentagon stated through the hom-components of the associator
isomorphisms. -/
theorem pentagon_iso_hom
    (W X Y Z : LogEndModule 𝕜) :
    (associatorIso (tensorObj W X) Y Z).hom ≫
        (associatorIso W X (tensorObj Y Z)).hom =
      tensorHom (associatorIso W X Y).hom (𝟙 Z) ≫
        (associatorIso W (tensorObj X Y) Z).hom ≫
        tensorHom (𝟙 W) (associatorIso X Y Z).hom := by
  exact pentagon_identity W X Y Z

end InfoGeometry.Categorical.LogEndModulePentagon
