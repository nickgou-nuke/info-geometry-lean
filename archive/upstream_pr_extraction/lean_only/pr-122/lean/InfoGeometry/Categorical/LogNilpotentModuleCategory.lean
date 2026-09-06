import InfoGeometry.Categorical.LogEndModuleNilpotentClosure

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
  Hom X Y := Hom X Y
  id X := 𝟙 X.toLogEndModule
  comp {X Y Z} f g := f ≫ g

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
  simp [tensorHom]

/-- Tensoring identities gives the identity. -/
@[simp]
theorem tensorHom_id (X Y : LogNilpotentModule 𝕜) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  apply LogEndModule.Hom.ext
  ext x y
  simp [tensorHom]

/-- Tensor product respects composition. -/
@[simp]
theorem tensorHom_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LogNilpotentModule 𝕜}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) =
      tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  apply LogEndModule.Hom.ext
  ext x y
  simp [tensorHom]

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

/-- The ambient tensor swap is an isomorphism in the finite-nilpotent category.

This is only the symmetric module-category baseline.  It is not asserted to be
the physical logarithmic CFT `R`-matrix braiding. -/
def symmetricSwapIso (X Y : LogNilpotentModule 𝕜) :
    tensorObj X Y ≅ tensorObj Y X :=
  { hom := LogEndModule.braidingHom X.toLogEndModule Y.toLogEndModule
    inv := LogEndModule.braidingHom Y.toLogEndModule X.toLogEndModule
    hom_inv_id := by
      apply LogEndModule.Hom.ext
      ext x y
      simp [LogEndModule.braidingHom]
    inv_hom_id := by
      apply LogEndModule.Hom.ext
      ext x y
      simp [LogEndModule.braidingHom] }

end LogNilpotentModule

end InfoGeometry.Categorical.LogNilpotentModuleCategory
