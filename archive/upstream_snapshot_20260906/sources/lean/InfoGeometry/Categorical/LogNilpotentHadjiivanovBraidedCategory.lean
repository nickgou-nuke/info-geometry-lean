import Mathlib.Tactic
import InfoGeometry.Categorical.LogNilpotentHadjiivanovHexagonAlgebra

/-!
# Natural Hadjiivanov braided category

The finite-nilpotent logarithmic category is already monoidal.  This file adds
the physical two-object braiding

`c_{X,Y} = exp(logShearBase • (N_X ⊗ N_Y)) ≫ τ_{X,Y}`

using only native Mathlib finite nilpotent exponentials and the repository's
existing tensor coherence maps.

As with the ambient symmetric baseline, the resulting `BraidedCategory` is
exposed as an explicit class-valued definition rather than a global instance.
This avoids typeclass diamonds and lets downstream developments choose the
physical or ambient braiding locally.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentHadjiivanovBraidedCategory

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalCategory
open InfoGeometry.Categorical.LogNilpotentHadjiivanovExponential
open InfoGeometry.Categorical.LogNilpotentHadjiivanovHexagonAlgebra
open InfoGeometry.Clifford.LogCftMonodromy

/-! ## Structural three-factor swaps -/

/-- Mathlib's `leftComm` lifted to the logarithmic category. -/
def leftCommIso (X Y Z : LogNilpotentModule ℂ) :
    X ⊗ (Y ⊗ Z) ≅ Y ⊗ (X ⊗ Z) where
  hom :=
    { hom := (TensorProduct.leftComm ℂ X Y Z).toLinearMap
      comm := by
        ext x y z
        simp [LinearMap.comp_apply, LogEndModule.tensorObj_N_tmul]
        module }
  inv :=
    { hom := (TensorProduct.leftComm ℂ X Y Z).symm.toLinearMap
      comm := by
        ext x y z
        simp [LinearMap.comp_apply, LogEndModule.tensorObj_N_tmul]
        module }
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    ext x y z
    simp
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    ext x y z
    simp

/-- Mathlib's `rightComm` lifted to the logarithmic category. -/
def rightCommIso (X Y Z : LogNilpotentModule ℂ) :
    (X ⊗ Y) ⊗ Z ≅ (X ⊗ Z) ⊗ Y where
  hom :=
    { hom := (TensorProduct.rightComm ℂ X Y Z).toLinearMap
      comm := by
        ext x y z
        simp [LinearMap.comp_apply, LogEndModule.tensorObj_N_tmul]
        module }
  inv :=
    { hom := (TensorProduct.rightComm ℂ X Y Z).symm.toLinearMap
      comm := by
        ext x y z
        simp [LinearMap.comp_apply, LogEndModule.tensorObj_N_tmul]
        module }
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    ext x y z
    simp
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    ext x y z
    simp

/-- `leftComm` is exactly associator--swap--associator on logarithmic objects. -/
theorem assoc_leftComm
    (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).hom ≫ (leftCommIso X Y Z).hom =
      LogNilpotentModule.tensorHom
          (LogNilpotentModule.symmetricSwapIso X Y).hom (𝟙 Z) ≫
        (α_ Y X Z).hom := by
  apply LogEndModule.Hom.ext
  ext x y z
  simp [leftCommIso, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorHom, LogNilpotentModule.symmetricSwapIso,
    LogEndModule.braidingHom, LinearMap.comp_apply,
    TensorProduct.map_tmul]

/-- The full swap of `X` past `Y ⊗ Z` factors through `leftComm` and the
remaining `X,Z` swap. -/
theorem swap_assoc_eq_leftComm_swap
    (X Y Z : LogNilpotentModule ℂ) :
    (LogNilpotentModule.symmetricSwapIso X (Y ⊗ Z)).hom ≫
        (α_ Y Z X).hom =
      (leftCommIso X Y Z).hom ≫
        LogNilpotentModule.tensorHom (𝟙 Y)
          (LogNilpotentModule.symmetricSwapIso X Z).hom := by
  apply LogEndModule.Hom.ext
  ext x y z
  simp [leftCommIso, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorHom, LogNilpotentModule.symmetricSwapIso,
    LogEndModule.braidingHom, LinearMap.comp_apply,
    TensorProduct.map_tmul]

/-- The inverse associator followed by `rightComm` is the inner `Y,Z` swap
followed by the inverse associator. -/
theorem assocInv_rightComm
    (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).inv ≫ (rightCommIso X Y Z).hom =
      LogNilpotentModule.tensorHom (𝟙 X)
          (LogNilpotentModule.symmetricSwapIso Y Z).hom ≫
        (α_ X Z Y).inv := by
  apply LogEndModule.Hom.ext
  ext x y z
  simp [rightCommIso, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorInv, LogNilpotentModule.symmetricSwapIso,
    LogEndModule.braidingHom, LinearMap.comp_apply,
    TensorProduct.map_tmul]

/-- Swapping `(X ⊗ Y)` past `Z` and reassociating factors through
`rightComm` followed by the `X,Z` swap. -/
theorem swap_assocInv_eq_rightComm_swap
    (X Y Z : LogNilpotentModule ℂ) :
    (LogNilpotentModule.symmetricSwapIso (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv =
      (rightCommIso X Y Z).hom ≫
        LogNilpotentModule.tensorHom
          (LogNilpotentModule.symmetricSwapIso X Z).hom (𝟙 Y) := by
  apply LogEndModule.Hom.ext
  ext x y z
  simp [rightCommIso, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorInv, LogNilpotentModule.symmetricSwapIso,
    LogEndModule.braidingHom, LinearMap.comp_apply,
    TensorProduct.map_tmul]

/-! ## Exponential legs as categorical morphisms -/

/-- `(X,Y)` exponential correction on the right-associated triple. -/
def rightExp12Hom (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    X ⊗ (Y ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) :=
  (α_ X Y Z).inv ≫
    LogNilpotentModule.tensorHom (crossExpHom p X Y) (𝟙 Z) ≫
      (α_ X Y Z).hom

/-- `(X,Z)` exponential correction on the right-associated triple. -/
def rightExp13Hom (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    X ⊗ (Y ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) :=
  (leftCommIso X Y Z).hom ≫
    LogNilpotentModule.tensorHom (𝟙 Y) (crossExpHom p X Z) ≫
      (leftCommIso X Y Z).inv

/-- Underlying endomorphism of the `(X,Y)` exponential leg. -/
theorem rightExp12Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (rightExp12Hom p X Y Z).hom =
      IsNilpotent.exp (p • rightCross12 X Y Z) := by
  rw [exp_rightCross12]
  apply LinearMap.ext
  intro t
  simp [rightExp12Hom, LinearEquiv.conjAlgEquiv_apply,
    Module.End.rTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorHom, LogEndModule.associatorInv,
    LinearMap.comp_apply]

/-- Underlying endomorphism of the `(X,Z)` exponential leg. -/
theorem rightExp13Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (rightExp13Hom p X Y Z).hom =
      IsNilpotent.exp (p • rightCross13 X Y Z) := by
  rw [exp_rightCross13]
  apply LinearMap.ext
  intro t
  simp [rightExp13Hom, leftCommIso, LinearEquiv.conjAlgEquiv_apply,
    Module.End.lTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LinearMap.comp_apply]

/-- The right-associated pair exponential factors categorically into its two
commuting legs. -/
theorem crossExpHom_right_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpHom p X (Y ⊗ Z) =
      rightExp12Hom p X Y Z ≫ rightExp13Hom p X Y Z := by
  apply LogEndModule.Hom.ext
  change crossExpEnd p X (Y ⊗ Z) =
    (rightExp13Hom p X Y Z).hom.comp (rightExp12Hom p X Y Z).hom
  rw [rightExp12Hom_hom, rightExp13Hom_hom,
    ← Module.End.mul_eq_comp]
  exact crossExpEnd_right_split p X Y Z

@[reassoc]
theorem assoc_rightExp12
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).hom ≫ rightExp12Hom p X Y Z =
      LogNilpotentModule.tensorHom (crossExpHom p X Y) (𝟙 Z) ≫
        (α_ X Y Z).hom := by
  simp [rightExp12Hom, Category.assoc]

@[reassoc]
theorem rightExp13_leftComm
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    rightExp13Hom p X Y Z ≫ (leftCommIso X Y Z).hom =
      (leftCommIso X Y Z).hom ≫
        LogNilpotentModule.tensorHom (𝟙 Y) (crossExpHom p X Z) := by
  simp [rightExp13Hom, Category.assoc]

/-! ## Left-associated exponential legs -/

/-- `(X,Z)` exponential correction on `(X ⊗ Y) ⊗ Z`. -/
def leftExp13Hom (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (X ⊗ Y) ⊗ Z ⟶ (X ⊗ Y) ⊗ Z :=
  (rightCommIso X Y Z).hom ≫
    LogNilpotentModule.tensorHom (crossExpHom p X Z) (𝟙 Y) ≫
      (rightCommIso X Y Z).inv

/-- `(Y,Z)` exponential correction on `(X ⊗ Y) ⊗ Z`. -/
def leftExp23Hom (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (X ⊗ Y) ⊗ Z ⟶ (X ⊗ Y) ⊗ Z :=
  (α_ X Y Z).hom ≫
    LogNilpotentModule.tensorHom (𝟙 X) (crossExpHom p Y Z) ≫
      (α_ X Y Z).inv

/-- Exponential transport for `leftCross13`. -/
theorem exp_leftCross13
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (p • leftCross13 X Y Z) =
      (((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y) (crossExpEnd p X Z)) := by
  let A : Module.End ℂ (X ⊗ Z) := p • crossEnd X Z
  let f := Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y
  let e := ((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm
  have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p X Z
  have hf := hA.map_exp f
  have hef := (hA.map f).map_exp e
  symm
  calc
    e (f (crossExpEnd p X Z)) = e (f (IsNilpotent.exp A)) := by rfl
    _ = e (IsNilpotent.exp (f A)) := by rw [hf]
    _ = IsNilpotent.exp (e (f A)) := hef
    _ = IsNilpotent.exp (p • leftCross13 X Y Z) := by
      congr 2
      simp [A, f, e, leftCross13]

/-- Exponential transport for `leftCross23`. -/
theorem exp_leftCross23
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (p • leftCross23 X Y Z) =
      (((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X) (crossExpEnd p Y Z)) := by
  let A : Module.End ℂ (Y ⊗ Z) := p • crossEnd Y Z
  let f := Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X
  let e := ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm
  have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p Y Z
  have hf := hA.map_exp f
  have hef := (hA.map f).map_exp e
  symm
  calc
    e (f (crossExpEnd p Y Z)) = e (f (IsNilpotent.exp A)) := by rfl
    _ = e (IsNilpotent.exp (f A)) := by rw [hf]
    _ = IsNilpotent.exp (e (f A)) := hef
    _ = IsNilpotent.exp (p • leftCross23 X Y Z) := by
      congr 2
      simp [A, f, e, leftCross23]

/-- Underlying endomorphism of the `(X,Z)` left-associated leg. -/
theorem leftExp13Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (leftExp13Hom p X Y Z).hom =
      IsNilpotent.exp (p • leftCross13 X Y Z) := by
  rw [exp_leftCross13]
  apply LinearMap.ext
  intro t
  simp [leftExp13Hom, rightCommIso, LinearEquiv.conjAlgEquiv_apply,
    Module.End.rTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LinearMap.comp_apply]

/-- Underlying endomorphism of the `(Y,Z)` left-associated leg. -/
theorem leftExp23Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (leftExp23Hom p X Y Z).hom =
      IsNilpotent.exp (p • leftCross23 X Y Z) := by
  rw [exp_leftCross23]
  apply LinearMap.ext
  intro t
  simp [leftExp23Hom, LinearEquiv.conjAlgEquiv_apply,
    Module.End.lTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorHom, LogEndModule.associatorInv,
    LinearMap.comp_apply]

/-- Reverse-order exponential split, chosen to match categorical composition in
the reverse hexagon. -/
theorem crossExpEnd_left_split_reverse
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpEnd p (X ⊗ Y) Z =
      IsNilpotent.exp (p • leftCross13 X Y Z) *
        IsNilpotent.exp (p • leftCross23 X Y Z) := by
  rw [crossExpEnd, crossEnd_left_decompose, smul_add]
  apply IsNilpotent.exp_add_of_commute
  · exact (leftCross_commute X Y Z).smul_left p |>.smul_right p
  · exact (leftCross13_isNilpotent X Y Z).smul p
  · exact (leftCross23_isNilpotent X Y Z).smul p

/-- Categorical reverse-order split. -/
theorem crossExpHom_left_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpHom p (X ⊗ Y) Z =
      leftExp23Hom p X Y Z ≫ leftExp13Hom p X Y Z := by
  apply LogEndModule.Hom.ext
  change crossExpEnd p (X ⊗ Y) Z =
    (leftExp13Hom p X Y Z).hom.comp (leftExp23Hom p X Y Z).hom
  rw [leftExp13Hom_hom, leftExp23Hom_hom,
    ← Module.End.mul_eq_comp]
  exact crossExpEnd_left_split_reverse p X Y Z

@[reassoc]
theorem assocInv_leftExp23
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).inv ≫ leftExp23Hom p X Y Z =
      LogNilpotentModule.tensorHom (𝟙 X) (crossExpHom p Y Z) ≫
        (α_ X Y Z).inv := by
  simp [leftExp23Hom, Category.assoc]

@[reassoc]
theorem leftExp13_rightComm
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    leftExp13Hom p X Y Z ≫ (rightCommIso X Y Z).hom =
      (rightCommIso X Y Z).hom ≫
        LogNilpotentModule.tensorHom (crossExpHom p X Z) (𝟙 Y) := by
  simp [leftExp13Hom, Category.assoc]

/-! ## Tensoring the corrected pair braiding -/

@[reassoc]
theorem tensorBraiding_right
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (logarithmicBraidingIso p X Y).hom ▷ Z =
      LogNilpotentModule.tensorHom (crossExpHom p X Y) (𝟙 Z) ≫
        LogNilpotentModule.tensorHom
          (LogNilpotentModule.symmetricSwapIso X Y).hom (𝟙 Z) := by
  change
    LogNilpotentModule.tensorHom
        (crossExpHom p X Y ≫
          (LogNilpotentModule.symmetricSwapIso X Y).hom) (𝟙 Z) = _
  simpa using
    (LogNilpotentModule.tensorHom_comp
      (crossExpHom p X Y)
      (LogNilpotentModule.symmetricSwapIso X Y).hom
      (𝟙 Z) (𝟙 Z))

@[reassoc]
theorem tensorBraiding_left
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Y ◁ (logarithmicBraidingIso p X Z).hom =
      LogNilpotentModule.tensorHom (𝟙 Y) (crossExpHom p X Z) ≫
        LogNilpotentModule.tensorHom (𝟙 Y)
          (LogNilpotentModule.symmetricSwapIso X Z).hom := by
  change
    LogNilpotentModule.tensorHom (𝟙 Y)
      (crossExpHom p X Z ≫
        (LogNilpotentModule.symmetricSwapIso X Z).hom) = _
  simpa using
    (LogNilpotentModule.tensorHom_comp
      (𝟙 Y) (𝟙 Y)
      (crossExpHom p X Z)
      (LogNilpotentModule.symmetricSwapIso X Z).hom)

/-! ## Hexagons -/

/-- Forward Mac Lane hexagon for the logarithmic exponential braiding. -/
theorem logarithmic_hexagon_forward
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).hom ≫
        (logarithmicBraidingIso p X (Y ⊗ Z)).hom ≫
        (α_ Y Z X).hom =
      ((logarithmicBraidingIso p X Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫
        (Y ◁ (logarithmicBraidingIso p X Z).hom) := by
  change
    (α_ X Y Z).hom ≫
        (crossExpHom p X (Y ⊗ Z) ≫
          (LogNilpotentModule.symmetricSwapIso X (Y ⊗ Z)).hom) ≫
        (α_ Y Z X).hom = _
  rw [crossExpHom_right_split]
  simp only [Category.assoc]
  rw [assoc_rightExp12]
  rw [swap_assoc_eq_leftComm_swap]
  rw [rightExp13_leftComm]
  rw [assoc_leftComm]
  rw [tensorBraiding_right, tensorBraiding_left]

/-- Reverse Mac Lane hexagon for the logarithmic exponential braiding. -/
theorem logarithmic_hexagon_reverse
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).inv ≫
        (logarithmicBraidingIso p (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv =
      (X ◁ (logarithmicBraidingIso p Y Z).hom) ≫
        (α_ X Z Y).inv ≫
        ((logarithmicBraidingIso p X Z).hom ▷ Y) := by
  change
    (α_ X Y Z).inv ≫
        (crossExpHom p (X ⊗ Y) Z ≫
          (LogNilpotentModule.symmetricSwapIso (X ⊗ Y) Z).hom) ≫
        (α_ Z X Y).inv = _
  rw [crossExpHom_left_split]
  simp only [Category.assoc]
  rw [assocInv_leftExp23]
  rw [swap_assocInv_eq_rightComm_swap]
  rw [leftExp13_rightComm]
  rw [assocInv_rightComm]
  change
    LogNilpotentModule.tensorHom (𝟙 X) (crossExpHom p Y Z) ≫
        LogNilpotentModule.tensorHom (𝟙 X)
          (LogNilpotentModule.symmetricSwapIso Y Z).hom ≫
        (α_ X Z Y).inv ≫
        LogNilpotentModule.tensorHom (crossExpHom p X Z) (𝟙 Y) ≫
        LogNilpotentModule.tensorHom
          (LogNilpotentModule.symmetricSwapIso X Z).hom (𝟙 Y) = _
  rw [← tensorBraiding_left p Y Z X]
  rw [← tensorBraiding_right p X Z Y]

/-- Mathlib-native physical braided structure at any complex shear parameter.

This is a class-valued definition, not a global instance. -/
noncomputable def logarithmicBraidedCategory (p : ℂ) :
    BraidedCategory (LogNilpotentModule ℂ) where
  braiding := logarithmicBraidingIso p
  braiding_naturality_right := logarithmicBraiding_naturality_right p
  braiding_naturality_left := logarithmicBraiding_naturality_left p
  hexagon_forward := logarithmic_hexagon_forward p
  hexagon_reverse := logarithmic_hexagon_reverse p

/-- Physical Hadjiivanov braided structure with `p = -2πi`. -/
noncomputable def hadjiivanovBraidedCategory :
    BraidedCategory (LogNilpotentModule ℂ) :=
  logarithmicBraidedCategory logShearBase

/-- Local readback of the physical braiding. -/
theorem hadjiivanov_braiding_hom
    (X Y : LogNilpotentModule ℂ) :
    letI : BraidedCategory (LogNilpotentModule ℂ) := hadjiivanovBraidedCategory
    (β_ X Y).hom = (hadjiivanovBraidingIso X Y).hom := by
  rfl

end InfoGeometry.Categorical.LogNilpotentHadjiivanovBraidedCategory
