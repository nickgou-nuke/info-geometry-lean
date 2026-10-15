import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Associator

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
      comm := by ext x; rfl }
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
      X.N x ⊗ₜ[𝕜] y + x ⊗ₜ[𝕜] Y.N y := rfl

/-- Tensor product of intertwining morphisms. -/
def tensorHom {X X' Y Y' : LogEndModule 𝕜}
    (f : X ⟶ X') (g : Y ⟶ Y') : tensorObj X Y ⟶ tensorObj X' Y' where
  hom := TensorProduct.map f.hom g.hom
  comm := by
    apply TensorProduct.ext'
    intro x y
    change (TensorProduct.map f.hom g.hom) ((tensorObj X Y).N (x ⊗ₜ y)) =
      (tensorObj X' Y').N ((TensorProduct.map f.hom g.hom) (x ⊗ₜ y))
    rw [tensorObj_N_tmul]
    rw [map_add]
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
    rw [tensorObj_N_tmul]
    rw [f.map_N, g.map_N]

@[simp]
theorem tensorHom_tmul {X X' Y Y' : LogEndModule 𝕜}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    (tensorHom f g).hom (x ⊗ₜ[𝕜] y) = f.hom x ⊗ₜ[𝕜] g.hom y := by
  exact TensorProduct.map_tmul _ _ _ _

/-- Tensoring identities gives the identity intertwiner. -/
@[simp]
theorem tensorHom_id (X Y : LogEndModule 𝕜) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  apply Hom.ext
  apply TensorProduct.ext'
  intro x y
  rfl

/-- Tensor product respects composition. -/
@[simp]
theorem tensorHom_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LogEndModule 𝕜}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) =
      tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  apply Hom.ext
  apply TensorProduct.ext'
  intro x y
  change f₂.hom (f₁.hom x) ⊗ₜ[𝕜] g₂.hom (g₁.hom y) =
    f₂.hom (f₁.hom x) ⊗ₜ[𝕜] g₂.hom (g₁.hom y)
  rfl

/-! ## Canonical coherence intertwiners -/

/-- Canonical tensor associator as a logarithmic intertwiner. -/
def associatorHom (X Y Z : LogEndModule 𝕜) :
    tensorObj (tensorObj X Y) Z ⟶ tensorObj X (tensorObj Y Z) where
  hom := (TensorProduct.assoc 𝕜 X Y Z).toLinearMap
  comm := by
    apply TensorProduct.ext_threefold
    intro x y z
    change (TensorProduct.assoc 𝕜 X.V Y.V Z.V)
        (((X.N x ⊗ₜ y + x ⊗ₜ Y.N y) ⊗ₜ z) + (x ⊗ₜ y) ⊗ₜ Z.N z) =
      X.N x ⊗ₜ (y ⊗ₜ z) + x ⊗ₜ (Y.N y ⊗ₜ z + y ⊗ₜ Z.N z)
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
    rw [map_add, map_add]
    rw [TensorProduct.assoc_tmul, TensorProduct.assoc_tmul, TensorProduct.assoc_tmul]
    abel

/-- Inverse associator as a logarithmic intertwiner. -/
def associatorInv (X Y Z : LogEndModule 𝕜) :
    tensorObj X (tensorObj Y Z) ⟶ tensorObj (tensorObj X Y) Z where
  hom := (TensorProduct.assoc 𝕜 X Y Z).symm.toLinearMap
  comm := by
    apply TensorProduct.ext_threefold'
    intro x y z
    change (TensorProduct.assoc 𝕜 X.V Y.V Z.V).symm
        (X.N x ⊗ₜ (y ⊗ₜ z) + x ⊗ₜ (Y.N y ⊗ₜ z + y ⊗ₜ Z.N z)) =
      ((X.N x ⊗ₜ y + x ⊗ₜ Y.N y) ⊗ₜ z) + (x ⊗ₜ y) ⊗ₜ Z.N z
    rw [TensorProduct.tmul_add, TensorProduct.add_tmul]
    rw [map_add, map_add]
    rw [TensorProduct.assoc_symm_tmul, TensorProduct.assoc_symm_tmul,
      TensorProduct.assoc_symm_tmul]
    abel

/-- The logarithmic associator is an isomorphism. -/
def associatorIso (X Y Z : LogEndModule 𝕜) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := associatorHom X Y Z
  inv := associatorInv X Y Z
  hom_inv_id := by
    apply Hom.ext
    apply LinearMap.ext
    intro w
    change (TensorProduct.assoc 𝕜 X.V Y.V Z.V).symm
        ((TensorProduct.assoc 𝕜 X.V Y.V Z.V) w) = w
    exact (TensorProduct.assoc 𝕜 X.V Y.V Z.V).left_inv w
  inv_hom_id := by
    apply Hom.ext
    apply LinearMap.ext
    intro w
    change (TensorProduct.assoc 𝕜 X.V Y.V Z.V)
        ((TensorProduct.assoc 𝕜 X.V Y.V Z.V).symm w) = w
    exact (TensorProduct.assoc 𝕜 X.V Y.V Z.V).right_inv w

@[simp]
theorem associatorHom_tmul (X Y Z : LogEndModule 𝕜)
    (x : X.V) (y : Y.V) (z : Z.V) :
    (associatorHom X Y Z).hom ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z) =
      x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z) := by
  change (TensorProduct.assoc 𝕜 X.V Y.V Z.V)
      ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z) = _
  rw [TensorProduct.assoc_tmul]

@[simp]
theorem associatorInv_tmul (X Y Z : LogEndModule 𝕜)
    (x : X.V) (y : Y.V) (z : Z.V) :
    (associatorInv X Y Z).hom (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z)) =
      (x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z := by
  change (TensorProduct.assoc 𝕜 X.V Y.V Z.V).symm
      (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z)) = _
  rw [TensorProduct.assoc_symm_tmul]

/-- Canonical tensor swap as a logarithmic intertwiner. -/
def braidingHom (X Y : LogEndModule 𝕜) : tensorObj X Y ⟶ tensorObj Y X where
  hom := (TensorProduct.comm 𝕜 X Y).toLinearMap
  comm := by
    apply TensorProduct.ext'
    intro x y
    change (TensorProduct.comm 𝕜 X.V Y.V)
        ((tensorObj X Y).N (x ⊗ₜ y)) =
      (tensorObj Y X).N
        ((TensorProduct.comm 𝕜 X.V Y.V) (x ⊗ₜ y))
    rw [tensorObj_N_tmul]
    rw [map_add]
    rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
    rw [tensorObj_N_tmul]
    rw [add_comm]

/-- The canonical swap is an involutive logarithmic braiding isomorphism. -/
def braidingIso (X Y : LogEndModule 𝕜) : tensorObj X Y ≅ tensorObj Y X where
  hom := braidingHom X Y
  inv := braidingHom Y X
  hom_inv_id := by
    apply Hom.ext
    apply LinearMap.ext
    intro w
    change (TensorProduct.comm 𝕜 Y.V X.V)
        ((TensorProduct.comm 𝕜 X.V Y.V) w) = w
    exact (TensorProduct.comm 𝕜 X.V Y.V).left_inv w
  inv_hom_id := by
    apply Hom.ext
    apply LinearMap.ext
    intro w
    change (TensorProduct.comm 𝕜 X.V Y.V)
        ((TensorProduct.comm 𝕜 Y.V X.V) w) = w
    exact (TensorProduct.comm 𝕜 Y.V X.V).left_inv w

end LogEndModule

end InfoGeometry.Categorical.LogEndModuleCategory
