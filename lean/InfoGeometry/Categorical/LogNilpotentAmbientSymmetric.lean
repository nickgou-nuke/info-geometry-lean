import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import InfoGeometry.Categorical.LogNilpotentMonoidalCategory
import InfoGeometry.Categorical.LogEndModuleHexagon

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
  apply TensorProduct.ext'
  intro x y
  change f.hom y ⊗ₜ[𝕜] x = f.hom y ⊗ₜ[𝕜] x
  rfl

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
  apply TensorProduct.ext'
  intro x z
  change z ⊗ₜ[𝕜] f.hom x = z ⊗ₜ[𝕜] f.hom x
  rfl

private theorem ambient_hexagon_forward
    (X Y Z : LogNilpotentModule 𝕜) :
    (α_ X Y Z).hom ≫
        (LogNilpotentModule.symmetricSwapIso X (Y ⊗ Z)).hom ≫
        (α_ Y Z X).hom =
      ((LogNilpotentModule.symmetricSwapIso X Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫
        (Y ◁ (LogNilpotentModule.symmetricSwapIso X Z).hom) := by
  exact InfoGeometry.Categorical.LogEndModuleHexagon.hexagon_iso_hom₁
    X.toLogEndModule Y.toLogEndModule Z.toLogEndModule

private theorem ambient_hexagon_reverse
    (X Y Z : LogNilpotentModule 𝕜) :
    (α_ X Y Z).inv ≫
        (LogNilpotentModule.symmetricSwapIso (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv =
      (X ◁ (LogNilpotentModule.symmetricSwapIso Y Z).hom) ≫
        (α_ X Z Y).inv ≫
        ((LogNilpotentModule.symmetricSwapIso X Z).hom ▷ Y) := by
  exact InfoGeometry.Categorical.LogEndModuleHexagon.hexagon_iso_hom₂
    X.toLogEndModule Y.toLogEndModule Z.toLogEndModule

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
  apply TensorProduct.ext'
  intro x y
  change TensorProduct.comm 𝕜 Y X (y ⊗ₜ[𝕜] x) = x ⊗ₜ[𝕜] y
  simp only [TensorProduct.comm_tmul, LinearMap.id_apply]

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
  change (LogNilpotentModule.symmetricSwapIso X Y).hom ≫
    (LogNilpotentModule.symmetricSwapIso Y X).hom = 𝟙 (X ⊗ Y)
  exact ambient_symmetry X Y

end InfoGeometry.Categorical.LogNilpotentAmbientSymmetric
