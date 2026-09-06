import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import InfoGeometry.Categorical.LogNilpotentMonoidalCategory

/-!
# InfoGeometry.Categorical.LogNilpotentAmbientSymmetric

Native Mathlib braided/symmetric packaging of the **ambient tensor swap** on
finite-nilpotent logarithmic modules.

This file intentionally does **not** register either structure as a global
instance.  Doing so would consume the unique typeclass slot
`BraidedCategory (LogNilpotentModule 𝕜)` with the involutive vector-space swap
and would obstruct the later non-symmetric physical LogCFT braiding.

Instead we expose class-valued definitions:

* `ambientBraidedCategory`;
* `ambientSymmetricCategory`.

They may be activated locally with `letI` whenever the symmetric carrier
baseline is desired.  The eventual Hadjiivanov/R-matrix braiding remains a
separate DAG node.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentAmbientSymmetric

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalCategory

universe u v

variable {𝕜 : Type u} [Field 𝕜]

private theorem ambient_braiding_naturality_right
    (X : LogNilpotentModule 𝕜)
    {Y Z : LogNilpotentModule 𝕜}
    (f : Y ⟶ Z) :
    X ◁ f ≫ (LogNilpotentModule.symmetricSwapIso X Z).hom =
      (LogNilpotentModule.symmetricSwapIso X Y).hom ≫ f ▷ X := by
  change
    LogNilpotentModule.tensorHom (𝟙 X) f ≫
        (LogNilpotentModule.symmetricSwapIso X Z).hom =
      (LogNilpotentModule.symmetricSwapIso X Y).hom ≫
        LogNilpotentModule.tensorHom f (𝟙 X)
  apply LogEndModule.Hom.ext
  ext x y
  simp [LogNilpotentModule.tensorHom, LogEndModule.tensorHom,
    LogNilpotentModule.symmetricSwapIso, LogEndModule.braidingHom,
    LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul]

private theorem ambient_braiding_naturality_left
    {X Y : LogNilpotentModule 𝕜}
    (f : X ⟶ Y) (Z : LogNilpotentModule 𝕜) :
    f ▷ Z ≫ (LogNilpotentModule.symmetricSwapIso Y Z).hom =
      (LogNilpotentModule.symmetricSwapIso X Z).hom ≫ Z ◁ f := by
  change
    LogNilpotentModule.tensorHom f (𝟙 Z) ≫
        (LogNilpotentModule.symmetricSwapIso Y Z).hom =
      (LogNilpotentModule.symmetricSwapIso X Z).hom ≫
        LogNilpotentModule.tensorHom (𝟙 Z) f
  apply LogEndModule.Hom.ext
  ext x z
  simp [LogNilpotentModule.tensorHom, LogEndModule.tensorHom,
    LogNilpotentModule.symmetricSwapIso, LogEndModule.braidingHom,
    LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul]

private theorem ambient_hexagon_forward
    (X Y Z : LogNilpotentModule 𝕜) :
    (α_ X Y Z).hom ≫
        (LogNilpotentModule.symmetricSwapIso X (Y ⊗ Z)).hom ≫
        (α_ Y Z X).hom =
      ((LogNilpotentModule.symmetricSwapIso X Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫
        (Y ◁ (LogNilpotentModule.symmetricSwapIso X Z).hom) := by
  apply LogEndModule.Hom.ext
  ext x y z
  simp [LogNilpotentModule.tensorHom, LogEndModule.tensorHom,
    LogNilpotentModule.associatorIso, LogEndModule.associatorHom,
    LogNilpotentModule.symmetricSwapIso, LogEndModule.braidingHom,
    LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.assoc_tmul,
    TensorProduct.comm_tmul]

private theorem ambient_hexagon_reverse
    (X Y Z : LogNilpotentModule 𝕜) :
    (α_ X Y Z).inv ≫
        (LogNilpotentModule.symmetricSwapIso (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv =
      (X ◁ (LogNilpotentModule.symmetricSwapIso Y Z).hom) ≫
        (α_ X Z Y).inv ≫
        ((LogNilpotentModule.symmetricSwapIso X Z).hom ▷ Y) := by
  apply LogEndModule.Hom.ext
  ext x y z
  simp [LogNilpotentModule.tensorHom, LogEndModule.tensorHom,
    LogNilpotentModule.associatorIso, LogEndModule.associatorInv,
    LogNilpotentModule.symmetricSwapIso, LogEndModule.braidingHom,
    LinearMap.comp_apply, TensorProduct.map_tmul,
    TensorProduct.assoc_symm_tmul, TensorProduct.comm_tmul]

/-- Mathlib-native braided structure supplied by the ambient vector-space swap.

This is a value, not a global instance. -/
noncomputable def ambientBraidedCategory :
    BraidedCategory (LogNilpotentModule 𝕜) where
  braiding := LogNilpotentModule.symmetricSwapIso
  braiding_naturality_right := ambient_braiding_naturality_right
  braiding_naturality_left := ambient_braiding_naturality_left
  hexagon_forward := ambient_hexagon_forward
  hexagon_reverse := ambient_hexagon_reverse

private theorem ambient_symmetry
    (X Y : LogNilpotentModule 𝕜) :
    (LogNilpotentModule.symmetricSwapIso X Y).hom ≫
        (LogNilpotentModule.symmetricSwapIso Y X).hom =
      𝟙 (X ⊗ Y) := by
  apply LogEndModule.Hom.ext
  ext x y
  simp [LogNilpotentModule.symmetricSwapIso, LogEndModule.braidingHom,
    LinearMap.comp_apply, TensorProduct.comm_tmul]

/-- Mathlib-native symmetric structure for the ambient carrier baseline.

This is deliberately non-global so that a future physical, non-involutive
LogCFT `BraidedCategory` can be installed on the core object type without
instance conflict. -/
noncomputable def ambientSymmetricCategory :
    SymmetricCategory (LogNilpotentModule 𝕜) where
  toBraidedCategory := ambientBraidedCategory
  symmetry := ambient_symmetry

/-- Local readback: the ambient structure supplies the ordinary swap as
Mathlib's braiding. -/
theorem ambient_braiding_hom
    (X Y : LogNilpotentModule 𝕜) :
    letI : BraidedCategory (LogNilpotentModule 𝕜) := ambientBraidedCategory
    (β_ X Y).hom = (LogNilpotentModule.symmetricSwapIso X Y).hom := by
  rfl

/-- Local readback of involutivity in the ambient symmetric baseline. -/
theorem ambient_braiding_involutive
    (X Y : LogNilpotentModule 𝕜) :
    letI : SymmetricCategory (LogNilpotentModule 𝕜) := ambientSymmetricCategory
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by
  exact SymmetricCategory.symmetry X Y

end InfoGeometry.Categorical.LogNilpotentAmbientSymmetric
