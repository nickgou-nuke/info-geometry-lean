import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# InfoGeometry.Categorical.LogEndModuleCategory

Tensor-stable categorical owner for a module equipped with a distinguished
endomorphism.

This is deliberately more general than a category of square-zero Jordan cells.
The reason is structural: if `N₁² = N₂² = 0`, then the primitive tensor
endomorphism

`N₁₂ = N₁ ⊗ id + id ⊗ N₂`

has cube zero but need not have square zero.  Therefore the square-zero objects
are not tensor-closed.

The present category remembers only the distinguished endomorphism.  Morphisms
are linear intertwiners.  Tensor product is defined by the primitive sum above,
and the canonical associator and tensor swap are lifted as intertwining
isomorphisms.  Nilpotence will be imposed later as a tensor-stable property with
an explicit nilpotency bound.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogEndModuleCategory

open CategoryTheory
open scoped TensorProduct

universe u v w

variable (𝕜 : Type u) [Field 𝕜]

/-- A `𝕜`-module with a distinguished logarithmic/endormorphism direction. -/
structure LogEndModule where
  V : Type v
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module 𝕜 V]
  N : Module.End 𝕜 V

attribute [instance] LogEndModule.instAddCommGroup LogEndModule.instModule

instance : CoeSort (LogEndModule 𝕜) (Type v) := ⟨LogEndModule.V⟩

namespace LogEndModule

variable {𝕜}

/-- Morphisms are linear maps intertwining the distinguished endomorphisms. -/
@[ext]
structure Hom (X Y : LogEndModule 𝕜) where
  hom : X →ₗ[𝕜] Y
  comm : hom.comp X.N = Y.N.comp hom

instance (X Y : LogEndModule 𝕜) : CoeFun (Hom X Y) (fun _ => X → Y) :=
  ⟨fun f => f.hom⟩

noncomputable instance : Category (LogEndModule 𝕜) where
  Hom X Y := Hom X Y
  id X :=
    { hom := LinearMap.id
      comm := by ext x <;> rfl }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      comm := by
        calc
          (g.hom.comp f.hom).comp X.N
              = g.hom.comp (f.hom.comp X.N) := by simp [LinearMap.comp_assoc]
          _ = g.hom.comp (Y.N.comp f.hom) := by rw [f.comm]
          _ = (g.hom.comp Y.N).comp f.hom := by simp [LinearMap.comp_assoc]
          _ = (Z.N.comp g.hom).comp f.hom := by rw [g.comm]
          _ = Z.N.comp (g.hom.comp f.hom) := by simp [LinearMap.comp_assoc] }

@[simp]
theorem hom_id (X : LogEndModule 𝕜) :
    (𝟙 X : X ⟶ X).hom = LinearMap.id := rfl

@[simp]
theorem hom_comp {X Y Z : LogEndModule 𝕜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Pointwise form of the intertwining equation. -/
@[simp]
theorem Hom.map_N {X Y : LogEndModule 𝕜} (f : X ⟶ Y) (x : X) :
    f.hom (X.N x) = Y.N (f.hom x) := by
  have h := LinearMap.congr_fun f.comm x
  simpa [LinearMap.comp_apply] using h

/-! ## Tensor product -/

/-- Tensor product object with primitive logarithmic endomorphism
`N_X ⊗ id + id ⊗ N_Y`. -/
def tensorObj (X Y : LogEndModule 𝕜) : LogEndModule 𝕜 where
  V := X ⊗[𝕜] Y
  N :=
    TensorProduct.map X.N (LinearMap.id : Module.End 𝕜 Y) +
      TensorProduct.map (LinearMap.id : Module.End 𝕜 X) Y.N

/-- Pure-tensor action of the tensor logarithmic endomorphism. -/
@[simp]
theorem tensorObj_N_tmul (X Y : LogEndModule 𝕜) (x : X) (y : Y) :
    (tensorObj X Y).N (x ⊗ₜ[𝕜] y) =
      X.N x ⊗ₜ[𝕜] y + x ⊗ₜ[𝕜] Y.N y := by
  simp [tensorObj, TensorProduct.map_tmul]

/-- Tensor product of intertwining morphisms. -/
def tensorHom {X X' Y Y' : LogEndModule 𝕜}
    (f : X ⟶ X') (g : Y ⟶ Y') : tensorObj X Y ⟶ tensorObj X' Y' where
  hom := TensorProduct.map f.hom g.hom
  comm := by
    ext x y
    simp [LinearMap.comp_apply, tensorObj_N_tmul, TensorProduct.map_tmul,
      f.map_N, g.map_N]

@[simp]
theorem tensorHom_tmul {X X' Y Y' : LogEndModule 𝕜}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    (tensorHom f g).hom (x ⊗ₜ[𝕜] y) = f.hom x ⊗ₜ[𝕜] g.hom y := by
  simp [tensorHom, TensorProduct.map_tmul]

/-- Tensoring identities gives the identity intertwiner. -/
@[simp]
theorem tensorHom_id (X Y : LogEndModule 𝕜) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  apply Hom.ext
  ext x y
  simp [tensorHom]

/-- Tensor product respects composition. -/
@[simp]
theorem tensorHom_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LogEndModule 𝕜}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) =
      tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  apply Hom.ext
  ext x y
  simp [tensorHom, LinearMap.comp_apply]

/-! ## Canonical coherence intertwiners -/

/-- Canonical tensor associator as a logarithmic intertwiner. -/
def associatorHom (X Y Z : LogEndModule 𝕜) :
    tensorObj (tensorObj X Y) Z ⟶ tensorObj X (tensorObj Y Z) where
  hom := (TensorProduct.assoc 𝕜 X Y Z).toLinearMap
  comm := by
    ext x y z
    simp [LinearMap.comp_apply, tensorObj_N_tmul, TensorProduct.assoc_tmul,
      add_assoc]

/-- Inverse associator as a logarithmic intertwiner. -/
def associatorInv (X Y Z : LogEndModule 𝕜) :
    tensorObj X (tensorObj Y Z) ⟶ tensorObj (tensorObj X Y) Z where
  hom := (TensorProduct.assoc 𝕜 X Y Z).symm.toLinearMap
  comm := by
    ext x y z
    simp [LinearMap.comp_apply, tensorObj_N_tmul,
      TensorProduct.assoc_symm_tmul, add_assoc]

/-- The logarithmic associator is an isomorphism. -/
def associatorIso (X Y Z : LogEndModule 𝕜) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := associatorHom X Y Z
  inv := associatorInv X Y Z
  hom_inv_id := by
    apply Hom.ext
    ext x y z
    simp [associatorHom, associatorInv]
  inv_hom_id := by
    apply Hom.ext
    ext x y z
    simp [associatorHom, associatorInv]

/-- Canonical tensor swap as a logarithmic intertwiner. -/
def braidingHom (X Y : LogEndModule 𝕜) : tensorObj X Y ⟶ tensorObj Y X where
  hom := (TensorProduct.comm 𝕜 X Y).toLinearMap
  comm := by
    ext x y
    simp [LinearMap.comp_apply, tensorObj_N_tmul, TensorProduct.comm_tmul,
      add_comm]

/-- The canonical swap is an involutive logarithmic braiding isomorphism. -/
def braidingIso (X Y : LogEndModule 𝕜) : tensorObj X Y ≅ tensorObj Y X where
  hom := braidingHom X Y
  inv := braidingHom Y X
  hom_inv_id := by
    apply Hom.ext
    ext x y
    simp [braidingHom]
  inv_hom_id := by
    apply Hom.ext
    ext x y
    simp [braidingHom]

end LogEndModule

end InfoGeometry.Categorical.LogEndModuleCategory
