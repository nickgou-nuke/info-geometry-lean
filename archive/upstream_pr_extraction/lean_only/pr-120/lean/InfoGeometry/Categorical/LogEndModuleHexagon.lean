import InfoGeometry.Categorical.LogEndModuleCategory

/-!
# InfoGeometry.Categorical.LogEndModuleHexagon

The two braided hexagon identities for the tensor-stable category of modules
with a distinguished logarithmic endomorphism.

The braiding is the canonical tensor swap, already proved to intertwine the
primitive logarithmic endomorphism.  These theorems compare the two explicit
three-object composites and therefore establish braided coherence at the
unpackaged theorem level.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogEndModuleHexagon

open CategoryTheory
open scoped TensorProduct
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule

universe u v

variable {𝕜 : Type u} [Field 𝕜]

/-- First braided hexagon.  Both sides map `(X ⊗ Y) ⊗ Z` to
`Y ⊗ (Z ⊗ X)`. -/
theorem hexagon_identity₁
    (X Y Z : LogEndModule 𝕜) :
    associatorHom X Y Z ≫
        braidingHom X (tensorObj Y Z) ≫
        associatorHom Y Z X =
      tensorHom (braidingHom X Y) (𝟙 Z) ≫
        associatorHom Y X Z ≫
        tensorHom (𝟙 Y) (braidingHom X Z) := by
  apply Hom.ext
  ext x y z
  simp [associatorHom, braidingHom, tensorHom, LinearMap.comp_apply,
    TensorProduct.assoc_tmul, TensorProduct.comm_tmul]

/-- Second braided hexagon.  Both sides map `X ⊗ (Y ⊗ Z)` to
`(Z ⊗ X) ⊗ Y`. -/
theorem hexagon_identity₂
    (X Y Z : LogEndModule 𝕜) :
    associatorInv X Y Z ≫
        braidingHom (tensorObj X Y) Z ≫
        associatorInv Z X Y =
      tensorHom (𝟙 X) (braidingHom Y Z) ≫
        associatorInv X Z Y ≫
        tensorHom (braidingHom X Z) (𝟙 Y) := by
  apply Hom.ext
  ext x y z
  simp [associatorInv, braidingHom, tensorHom, LinearMap.comp_apply,
    TensorProduct.assoc_symm_tmul, TensorProduct.comm_tmul]

/-- First hexagon through the hom-components of the lifted isomorphisms. -/
theorem hexagon_iso_hom₁
    (X Y Z : LogEndModule 𝕜) :
    (associatorIso X Y Z).hom ≫
        (braidingIso X (tensorObj Y Z)).hom ≫
        (associatorIso Y Z X).hom =
      tensorHom (braidingIso X Y).hom (𝟙 Z) ≫
        (associatorIso Y X Z).hom ≫
        tensorHom (𝟙 Y) (braidingIso X Z).hom := by
  exact hexagon_identity₁ X Y Z

/-- Second hexagon through the inverse associators and braiding hom-components. -/
theorem hexagon_iso_hom₂
    (X Y Z : LogEndModule 𝕜) :
    (associatorIso X Y Z).inv ≫
        (braidingIso (tensorObj X Y) Z).hom ≫
        (associatorIso Z X Y).inv =
      tensorHom (𝟙 X) (braidingIso Y Z).hom ≫
        (associatorIso X Z Y).inv ≫
        tensorHom (braidingIso X Z).hom (𝟙 Y) := by
  exact hexagon_identity₂ X Y Z

end InfoGeometry.Categorical.LogEndModuleHexagon
