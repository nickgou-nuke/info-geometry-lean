import InfoGeometry.Categorical.LogEndModuleNilpotentClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Categorical.LogNilpotentModuleCategory

Tensor-closed category of modules with a distinguished finite-nilpotent
endomorphism.

Unlike a category restricted to square-zero/rank-two Jordan cells, this class is
closed under the primitive tensor product.  An object carries an explicit
nilpotency order `r` and a proof `N^r = 0`; tensoring orders `m,n` produces the
valid bound `m+n-1`.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentModuleCategory

open CategoryTheory
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure

universe u v

variable (𝕜 : Type u) [Field 𝕜]

/-- A logarithmic module with an explicitly certified finite nilpotency order. -/
structure LogNilpotentModule where
  toLogEndModule : LogEndModule 𝕜
  nilpotencyOrder : ℕ
  nilpotent : toLogEndModule.N ^ nilpotencyOrder = 0

namespace LogNilpotentModule

variable {𝕜}

instance : CoeSort (LogNilpotentModule 𝕜) (Type v) :=
  ⟨fun X => X.toLogEndModule.V⟩

instance (X : LogNilpotentModule 𝕜) : AddCommGroup X :=
  X.toLogEndModule.instAddCommGroup

instance (X : LogNilpotentModule 𝕜) : Module 𝕜 X :=
  X.toLogEndModule.instModule

/-- Distinguished nilpotent endomorphism of an object. -/
abbrev N (X : LogNilpotentModule 𝕜) : Module.End 𝕜 X :=
  X.toLogEndModule.N

/-- Morphisms are exactly the underlying logarithmic intertwiners. -/
abbrev Hom (X Y : LogNilpotentModule 𝕜) :=
  LogEndModule.Hom X.toLogEndModule Y.toLogEndModule

instance (X Y : LogNilpotentModule 𝕜) : CoeFun (Hom X Y) (fun _ => X → Y) :=
  ⟨fun f => f.hom⟩

noncomputable instance : Category (LogNilpotentModule 𝕜) where
  Hom X Y := LogEndModule.Hom X.toLogEndModule Y.toLogEndModule
  id X :=
    { hom := LinearMap.id
      comm := by ext x <;> rfl }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      comm := by
        calc
          (g.hom.comp f.hom).comp X.toLogEndModule.N =
              g.hom.comp (f.hom.comp X.toLogEndModule.N) := by
                simp [LinearMap.comp_assoc]
          _ = g.hom.comp (Y.toLogEndModule.N.comp f.hom) := by rw [f.comm]
          _ = (g.hom.comp Y.toLogEndModule.N).comp f.hom := by
                simp [LinearMap.comp_assoc]
          _ = (Z.toLogEndModule.N.comp g.hom).comp f.hom := by rw [g.comm]
          _ = Z.toLogEndModule.N.comp (g.hom.comp f.hom) := by
                simp [LinearMap.comp_assoc] }

@[simp]
theorem hom_id (X : LogNilpotentModule 𝕜) :
    (𝟙 X : X ⟶ X).hom = LinearMap.id := rfl

@[simp]
theorem hom_comp {X Y Z : LogNilpotentModule 𝕜}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- The stored nilpotency certificate. -/
theorem N_pow_order_eq_zero (X : LogNilpotentModule 𝕜) :
    X.N ^ X.nilpotencyOrder = 0 :=
  X.nilpotent

/-- Tensor product in the finite-nilpotent logarithmic category. -/
def tensorObj (X Y : LogNilpotentModule 𝕜) : LogNilpotentModule 𝕜 where
  toLogEndModule := LogEndModule.tensorObj X.toLogEndModule Y.toLogEndModule
  nilpotencyOrder := X.nilpotencyOrder + Y.nilpotencyOrder - 1
  nilpotent :=
    tensorObj_N_pow_add_sub_one_eq_zero
      X.toLogEndModule Y.toLogEndModule
      X.nilpotencyOrder Y.nilpotencyOrder
      X.nilpotent Y.nilpotent

/-- Tensor product of logarithmic intertwining morphisms. -/
def tensorHom {X X' Y Y' : LogNilpotentModule 𝕜}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj X Y ⟶ tensorObj X' Y' :=
  LogEndModule.tensorHom f g

@[simp]
theorem tensorHom_tmul {X X' Y Y' : LogNilpotentModule 𝕜}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    (tensorHom f g).hom (x ⊗ₜ[𝕜] y) = f.hom x ⊗ₜ[𝕜] g.hom y := by
  exact LogEndModule.tensorHom_tmul f g x y

/-- Tensoring identities gives the identity. -/
@[simp]
theorem tensorHom_id (X Y : LogNilpotentModule 𝕜) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  exact LogEndModule.tensorHom_id X.toLogEndModule Y.toLogEndModule

/-- Tensor product respects composition. -/
@[simp]
theorem tensorHom_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LogNilpotentModule 𝕜}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) =
      tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  exact LogEndModule.tensorHom_comp f₁ f₂ g₁ g₂

/-- The canonical reassociator is a morphism in the finite-nilpotent category. -/
def associatorIso (X Y Z : LogNilpotentModule 𝕜) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  { hom := LogEndModule.associatorHom
      X.toLogEndModule Y.toLogEndModule Z.toLogEndModule
    inv := LogEndModule.associatorInv
      X.toLogEndModule Y.toLogEndModule Z.toLogEndModule
    hom_inv_id := by
      apply LogEndModule.Hom.ext
      ext x y z
      simp [LogEndModule.associatorHom, LogEndModule.associatorInv]
    inv_hom_id := by
      apply LogEndModule.Hom.ext
      ext x y z
      simp [LogEndModule.associatorHom, LogEndModule.associatorInv] }

@[simp]
theorem associatorHom_tmul (X Y Z : LogNilpotentModule 𝕜)
    (x : X.toLogEndModule.V) (y : Y.toLogEndModule.V)
    (z : Z.toLogEndModule.V) :
    (associatorIso X Y Z).hom.hom ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z) =
      x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z) := by
  exact LogEndModule.associatorHom_tmul
    X.toLogEndModule Y.toLogEndModule Z.toLogEndModule x y z

@[simp]
theorem associatorInv_tmul (X Y Z : LogNilpotentModule 𝕜)
    (x : X.toLogEndModule.V) (y : Y.toLogEndModule.V)
    (z : Z.toLogEndModule.V) :
    (associatorIso X Y Z).inv.hom (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z)) =
      (x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z := by
  exact LogEndModule.associatorInv_tmul
    X.toLogEndModule Y.toLogEndModule Z.toLogEndModule x y z

/-- The ambient tensor swap is an isomorphism in the finite-nilpotent category.

This is only the symmetric module-category baseline.  It is not asserted to be
the physical logarithmic CFT `R`-matrix braiding. -/
def symmetricSwapIso (X Y : LogNilpotentModule 𝕜) :
    tensorObj X Y ≅ tensorObj Y X :=
  { hom := LogEndModule.braidingHom X.toLogEndModule Y.toLogEndModule
    inv := LogEndModule.braidingHom Y.toLogEndModule X.toLogEndModule
    hom_inv_id := by
      apply LogEndModule.Hom.ext
      apply TensorProduct.ext'
      intro x y
      change (TensorProduct.comm 𝕜 Y.toLogEndModule.V X.toLogEndModule.V)
          ((TensorProduct.comm 𝕜 X.toLogEndModule.V Y.toLogEndModule.V)
            (x ⊗ₜ[𝕜] y)) = x ⊗ₜ[𝕜] y
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul]
    inv_hom_id := by
      apply LogEndModule.Hom.ext
      apply TensorProduct.ext'
      intro x y
      change (TensorProduct.comm 𝕜 X.toLogEndModule.V Y.toLogEndModule.V)
          ((TensorProduct.comm 𝕜 Y.toLogEndModule.V X.toLogEndModule.V)
            (x ⊗ₜ[𝕜] y)) = x ⊗ₜ[𝕜] y
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul] }

end LogNilpotentModule

end InfoGeometry.Categorical.LogNilpotentModuleCategory
