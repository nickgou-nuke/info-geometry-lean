import Mathlib.CategoryTheory.Monoidal.Category
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.LogEndModulePentagon
import InfoGeometry.Categorical.LogNilpotentMonoidalUnit

/-!
# InfoGeometry.Categorical.LogNilpotentMonoidalCategory

Mathlib monoidal-category packaging for the tensor-closed category of finite
nilpotent logarithmic modules.

The mathematical work is owned by the preceding DAG nodes:

* tensor closure with order bound `m+n-1`;
* tensor functoriality on logarithmic intertwiners;
* lifted tensor associators;
* the zero-nilpotent scalar unit and its unitors;
* pentagon and triangle coherence.

This file packages that data as `MonoidalCategoryStruct` and
`MonoidalCategory`.  It deliberately does not install a `BraidedCategory`:
the ambient tensor swap is only the symmetric module-category baseline, while
the physical LogCFT braiding still requires two-object monodromy/R-matrix data.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentMonoidalCategory

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalUnit

universe u v

variable {𝕜 : Type u} [Field 𝕜]

/-- The already-constructed logarithmic tensor data, exposed through Mathlib's
monoidal-structure interface. -/
noncomputable instance logNilpotentMonoidalCategoryStruct :
    MonoidalCategoryStruct (LogNilpotentModule 𝕜) where
  tensorObj := LogNilpotentModule.tensorObj
  whiskerLeft X _ _ f := LogNilpotentModule.tensorHom (𝟙 X) f
  whiskerRight f Y := LogNilpotentModule.tensorHom f (𝟙 Y)
  tensorHom := LogNilpotentModule.tensorHom
  tensorUnit := unitObject
  associator := LogNilpotentModule.associatorIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso

/-- Naturality of the lifted logarithmic associator. -/
theorem associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LogNilpotentModule 𝕜}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    LogNilpotentModule.tensorHom
          (LogNilpotentModule.tensorHom f₁ f₂) f₃ ≫
        (LogNilpotentModule.associatorIso Y₁ Y₂ Y₃).hom =
      (LogNilpotentModule.associatorIso X₁ X₂ X₃).hom ≫
        LogNilpotentModule.tensorHom f₁
          (LogNilpotentModule.tensorHom f₂ f₃) := by
  apply LogEndModule.Hom.ext
  apply TensorProduct.ext_threefold
  intro x₁ x₂ x₃
  change (TensorProduct.assoc 𝕜 Y₁.toLogEndModule.V Y₂.toLogEndModule.V
      Y₃.toLogEndModule.V)
      ((TensorProduct.map (TensorProduct.map f₁.hom f₂.hom) f₃.hom)
        (x₁ ⊗ₜ[𝕜] x₂ ⊗ₜ[𝕜] x₃)) =
    (TensorProduct.map f₁.hom (TensorProduct.map f₂.hom f₃.hom))
      ((TensorProduct.assoc 𝕜 X₁.toLogEndModule.V X₂.toLogEndModule.V
        X₃.toLogEndModule.V) (x₁ ⊗ₜ[𝕜] x₂ ⊗ₜ[𝕜] x₃))
  simp only [TensorProduct.map_tmul, TensorProduct.assoc_tmul]

/-- Naturality of the lifted left unitor. -/
theorem leftUnitor_naturality
    {X Y : LogNilpotentModule 𝕜} (f : X ⟶ Y) :
    LogNilpotentModule.tensorHom (𝟙 (unitObject : LogNilpotentModule 𝕜)) f ≫
        (leftUnitorIso Y).hom =
      (leftUnitorIso X).hom ≫ f := by
  apply LogEndModule.Hom.ext
  apply TensorProduct.ext'
  intro c x
  change TensorProduct.lid 𝕜 Y.toLogEndModule.V
      (TensorProduct.map LinearMap.id f.hom (c ⊗ₜ[𝕜] x)) =
    f.hom (TensorProduct.lid 𝕜 X.toLogEndModule.V (c ⊗ₜ[𝕜] x))
  simp [LogNilpotentModule.tensorHom, LogEndModule.tensorHom,
    leftUnitorIso, leftUnitorHom, LinearMap.comp_apply,
    TensorProduct.map_tmul]

/-- Naturality of the lifted right unitor. -/
theorem rightUnitor_naturality
    {X Y : LogNilpotentModule 𝕜} (f : X ⟶ Y) :
    LogNilpotentModule.tensorHom f (𝟙 (unitObject : LogNilpotentModule 𝕜)) ≫
        (rightUnitorIso Y).hom =
      (rightUnitorIso X).hom ≫ f := by
  apply LogEndModule.Hom.ext
  apply TensorProduct.ext'
  intro x c
  change TensorProduct.rid 𝕜 Y.toLogEndModule.V
      (TensorProduct.map f.hom LinearMap.id (x ⊗ₜ[𝕜] c)) =
    f.hom (TensorProduct.rid 𝕜 X.toLogEndModule.V (x ⊗ₜ[𝕜] c))
  simp [LogNilpotentModule.tensorHom, LogEndModule.tensorHom,
    rightUnitorIso, rightUnitorHom, LinearMap.comp_apply,
    TensorProduct.map_tmul]

/-- Mac Lane's pentagon for the finite-nilpotent logarithmic category. -/
theorem pentagon_identity
    (W X Y Z : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorHom
          (LogNilpotentModule.associatorIso W X Y).hom (𝟙 Z) ≫
        (LogNilpotentModule.associatorIso W
          (LogNilpotentModule.tensorObj X Y) Z).hom ≫
        LogNilpotentModule.tensorHom (𝟙 W)
          (LogNilpotentModule.associatorIso X Y Z).hom =
      (LogNilpotentModule.associatorIso
          (LogNilpotentModule.tensorObj W X) Y Z).hom ≫
      (LogNilpotentModule.associatorIso W X
          (LogNilpotentModule.tensorObj Y Z)).hom := by
  exact (LogEndModulePentagon.pentagon_identity
    W.toLogEndModule X.toLogEndModule Y.toLogEndModule Z.toLogEndModule).symm

/-- The finite-nilpotent logarithmic modules form a Mathlib monoidal category. -/
noncomputable instance logNilpotentMonoidalCategory :
    MonoidalCategory (LogNilpotentModule 𝕜) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X Y =>
      LogNilpotentModule.tensorHom_id X Y)
    (id_tensorHom := fun X {Y₁ Y₂} f => rfl)
    (tensorHom_id := fun {X₁ X₂} f Y => rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      exact
        (LogNilpotentModule.tensorHom_comp f₁ g₁ f₂ g₂).symm)
    (associator_naturality := fun f₁ f₂ f₃ =>
      associator_naturality f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => leftUnitor_naturality f)
    (rightUnitor_naturality := fun f => rightUnitor_naturality f)
    (pentagon := pentagon_identity)
    (triangle := triangle_identity)

/-- Mathlib's tensor notation reduces to the native logarithmic tensor object. -/
@[simp]
theorem tensorObj_eq (X Y : LogNilpotentModule 𝕜) :
    X ⊗ Y = LogNilpotentModule.tensorObj X Y :=
  rfl

/-- Mathlib's tensor unit is the zero-nilpotent scalar module. -/
@[simp]
theorem tensorUnit_eq :
    (𝟙_ (LogNilpotentModule 𝕜)) = unitObject :=
  rfl

end InfoGeometry.Categorical.LogNilpotentMonoidalCategory
