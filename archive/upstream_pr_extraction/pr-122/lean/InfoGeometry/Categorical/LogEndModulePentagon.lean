import InfoGeometry.Categorical.LogEndModuleCategory

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

variable {𝕜 : Type u} [Field 𝕜]

/-- Mac Lane's pentagon identity for the lifted logarithmic associator. -/
theorem pentagon_identity
    (W X Y Z : LogEndModule 𝕜) :
    associatorHom (tensorObj W X) Y Z ≫
        associatorHom W X (tensorObj Y Z) =
      tensorHom (associatorHom W X Y) (𝟙 Z) ≫
        associatorHom W (tensorObj X Y) Z ≫
        tensorHom (𝟙 W) (associatorHom X Y Z) := by
  apply Hom.ext
  ext w x y z
  simp [associatorHom, tensorHom, LinearMap.comp_apply,
    TensorProduct.assoc_tmul]

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
