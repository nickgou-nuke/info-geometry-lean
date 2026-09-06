import Mathlib.Tactic
import Mathlib.Algebra.Algebra.Equiv
import InfoGeometry.Categorical.LogNilpotentPhysicalBraidingHexagon
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Native physical braided structure on finite-nilpotent logarithmic modules

`LogNilpotentPhysicalBraiding` owns the natural two-object exchange

`c_{X,Y}(p) = exp(p N_X⊗N_Y) ≫ τ_{X,Y}`,

and `LogNilpotentPhysicalBraidingHexagon` owns the right-associated exponential
factorization.  This file closes the remaining categorical coherence:

* the complementary left-associated factorization;
* transport of the two exponential legs through associator/commutor maps;
* both Mac Lane hexagons;
* a Mathlib-native `BraidedCategory` value.

The braided structure is deliberately a class-valued `def`, not a global
instance.  Downstream code can therefore choose explicitly between the ambient
symmetric swap and the physical logarithmic braiding without a typeclass
diamond.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentPhysicalBraidedCategory

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalCategory
open InfoGeometry.Categorical.LogNilpotentPhysicalBraiding
open InfoGeometry.Categorical.LogNilpotentPhysicalBraidingHexagon
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

/-- `leftComm` is associator--swap--associator. -/
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
    LogEndModule.braidingHom, LinearMap.comp_apply, TensorProduct.map_tmul]

/-- Full swap past a right-associated tensor product factors through
`leftComm`. -/
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
    LogEndModule.braidingHom, LinearMap.comp_apply, TensorProduct.map_tmul]

/-- Inverse associator followed by `rightComm` is the inner `Y,Z` swap followed
by the inverse associator. -/
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
    LogEndModule.braidingHom, LinearMap.comp_apply, TensorProduct.map_tmul]

/-- Full swap in the reverse hexagon factors through `rightComm`. -/
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
    LogEndModule.braidingHom, LinearMap.comp_apply, TensorProduct.map_tmul]

/-! ## Right-associated exponential legs -/

/-- The existing first right-associated triple leg is the associator transport
of the pair cross generator. -/
theorem scaledLeftTripleCross_eq_transport
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledLeftTripleCross p X Y Z =
      ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z) (scaledCrossEnd p X Y)) := by
  ext x y z
  simp [scaledLeftTripleCross, leftTripleCross,
    LinearEquiv.conjAlgEquiv_apply, Module.End.rTensorAlgHom,
    scaledCrossEnd, crossTensorEnd, LinearMap.comp_apply]

/-- The second right-associated triple leg is the `leftComm` pullback of the
`(X,Z)` pair cross generator. -/
theorem scaledRightTripleCross_eq_transport
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledRightTripleCross p X Y Z =
      (((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y) (scaledCrossEnd p X Z)) := by
  ext x y z
  simp [scaledRightTripleCross, rightTripleCross,
    LinearEquiv.conjAlgEquiv_apply, Module.End.lTensorAlgHom,
    scaledCrossEnd, crossTensorEnd, LinearMap.comp_apply]

/-- Exponential transport for the `(X,Y)` triple leg. -/
theorem exp_scaledLeftTripleCross
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledLeftTripleCross p X Y Z) =
      ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z) (crossExpEnd p X Y)) := by
  rw [scaledLeftTripleCross_eq_transport]
  let f := Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z
  let e := (TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ
  have hD := scaledCrossEnd_isNilpotent p X Y
  rw [← hD.map_exp f, ← (hD.map f).map_exp e]

/-- Exponential transport for the `(X,Z)` triple leg. -/
theorem exp_scaledRightTripleCross
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledRightTripleCross p X Y Z) =
      (((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y) (crossExpEnd p X Z)) := by
  rw [scaledRightTripleCross_eq_transport]
  let f := Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y
  let e := ((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm
  have hD := scaledCrossEnd_isNilpotent p X Z
  rw [← hD.map_exp f, ← (hD.map f).map_exp e]

/-- The right-associated factorization in the order matching categorical
left-to-right composition. -/
theorem crossExpEnd_tensorObj_factorization_rev
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpEnd p X (LogNilpotentModule.tensorObj Y Z) =
      IsNilpotent.exp (scaledRightTripleCross p X Y Z) *
        IsNilpotent.exp (scaledLeftTripleCross p X Y Z) := by
  rw [crossExpEnd, scaledCrossEnd_tensorObj_eq_add, add_comm]
  exact IsNilpotent.exp_add_of_commute
    (scaledTripleCross_commute p X Y Z).symm
    (scaledRightTripleCross_isNilpotent p X Y Z)
    (scaledLeftTripleCross_isNilpotent p X Y Z)

/-- `(X,Y)` exponential correction on `X ⊗ (Y ⊗ Z)`. -/
def rightExp12Hom (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    X ⊗ (Y ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) :=
  (α_ X Y Z).inv ≫
    LogNilpotentModule.tensorHom (crossExpHom p X Y) (𝟙 Z) ≫
      (α_ X Y Z).hom

/-- `(X,Z)` exponential correction on `X ⊗ (Y ⊗ Z)`. -/
def rightExp13Hom (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    X ⊗ (Y ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) :=
  (leftCommIso X Y Z).hom ≫
    LogNilpotentModule.tensorHom (𝟙 Y) (crossExpHom p X Z) ≫
      (leftCommIso X Y Z).inv

@[simp]
theorem rightExp12Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (rightExp12Hom p X Y Z).hom =
      IsNilpotent.exp (scaledLeftTripleCross p X Y Z) := by
  rw [exp_scaledLeftTripleCross]
  apply LinearMap.ext
  intro t
  simp [rightExp12Hom, LinearEquiv.conjAlgEquiv_apply,
    Module.End.rTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorHom, LogEndModule.associatorInv,
    LinearMap.comp_apply]

@[simp]
theorem rightExp13Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (rightExp13Hom p X Y Z).hom =
      IsNilpotent.exp (scaledRightTripleCross p X Y Z) := by
  rw [exp_scaledRightTripleCross]
  apply LinearMap.ext
  intro t
  simp [rightExp13Hom, leftCommIso, LinearEquiv.conjAlgEquiv_apply,
    Module.End.lTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LinearMap.comp_apply]

/-- Categorical right-associated exponential splitting. -/
theorem crossExpHom_right_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpHom p X (Y ⊗ Z) =
      rightExp12Hom p X Y Z ≫ rightExp13Hom p X Y Z := by
  apply LogEndModule.Hom.ext
  change crossExpEnd p X (Y ⊗ Z) =
    (rightExp13Hom p X Y Z).hom.comp (rightExp12Hom p X Y Z).hom
  rw [rightExp12Hom_hom, rightExp13Hom_hom,
    ← Module.End.mul_eq_comp]
  exact crossExpEnd_tensorObj_factorization_rev p X Y Z

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

/-! ## Left-associated exponential splitting -/

/-- `p N_X ⊗ id_Y ⊗ N_Z` on `(X ⊗ Y) ⊗ Z`. -/
def scaledLeftCross13
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ ((X ⊗ Y) ⊗ Z) :=
  p • TensorProduct.map
    (TensorProduct.map X.N (LinearMap.id : Module.End ℂ Y)) Z.N

/-- `p id_X ⊗ N_Y ⊗ N_Z` on `(X ⊗ Y) ⊗ Z`. -/
def scaledLeftCross23
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ ((X ⊗ Y) ⊗ Z) :=
  p • TensorProduct.map
    (TensorProduct.map (LinearMap.id : Module.End ℂ X) Y.N) Z.N

/-- The cross generator for `(X ⊗ Y,Z)` splits into the two left-associated
legs. -/
theorem scaledCrossEnd_left_eq_add
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledCrossEnd p (X ⊗ Y) Z =
      scaledLeftCross13 p X Y Z + scaledLeftCross23 p X Y Z := by
  ext x y z
  simp [scaledCrossEnd, crossTensorEnd, scaledLeftCross13,
    scaledLeftCross23, LogEndModule.tensorObj_N_tmul,
    TensorProduct.map_tmul, smul_add]

/-- The two left-associated legs commute. -/
theorem scaledLeftCross_commute
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Commute (scaledLeftCross13 p X Y Z) (scaledLeftCross23 p X Y Z) := by
  apply Commute.eq
  ext x y z
  simp [scaledLeftCross13, scaledLeftCross23,
    Module.End.mul_eq_comp, LinearMap.comp_apply, TensorProduct.map_tmul,
    smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The `(X,Z)` left-associated leg is nilpotent. -/
theorem scaledLeftCross13_isNilpotent
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (scaledLeftCross13 p X Y Z) := by
  refine ⟨X.nilpotencyOrder, ?_⟩
  have hx := X.nilpotent
  rw [scaledLeftCross13]
  induction X.nilpotencyOrder with
  | zero => simpa using hx
  | succ n ih =>
      ext x y z
      simp [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply,
        TensorProduct.map_tmul, hx]

/-- The `(Y,Z)` left-associated leg is nilpotent. -/
theorem scaledLeftCross23_isNilpotent
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (scaledLeftCross23 p X Y Z) := by
  refine ⟨Y.nilpotencyOrder, ?_⟩
  have hy := Y.nilpotent
  rw [scaledLeftCross23]
  induction Y.nilpotencyOrder with
  | zero => simpa using hy
  | succ n ih =>
      ext x y z
      simp [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply,
        TensorProduct.map_tmul, hy]

/-- Exact left-associated exponential factorization. -/
theorem crossExpEnd_left_factorization
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpEnd p (X ⊗ Y) Z =
      IsNilpotent.exp (scaledLeftCross13 p X Y Z) *
        IsNilpotent.exp (scaledLeftCross23 p X Y Z) := by
  rw [crossExpEnd, scaledCrossEnd_left_eq_add]
  exact IsNilpotent.exp_add_of_commute
    (scaledLeftCross_commute p X Y Z)
    (scaledLeftCross13_isNilpotent p X Y Z)
    (scaledLeftCross23_isNilpotent p X Y Z)

/-- The `(X,Z)` left leg is the `rightComm` pullback of the pair generator. -/
theorem scaledLeftCross13_eq_transport
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledLeftCross13 p X Y Z =
      (((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y) (scaledCrossEnd p X Z)) := by
  ext x y z
  simp [scaledLeftCross13, LinearEquiv.conjAlgEquiv_apply,
    Module.End.rTensorAlgHom, scaledCrossEnd, crossTensorEnd,
    LinearMap.comp_apply]

/-- The `(Y,Z)` left leg is the inverse-associator pullback of the pair
generator. -/
theorem scaledLeftCross23_eq_transport
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledLeftCross23 p X Y Z =
      (((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X) (scaledCrossEnd p Y Z)) := by
  ext x y z
  simp [scaledLeftCross23, LinearEquiv.conjAlgEquiv_apply,
    Module.End.lTensorAlgHom, scaledCrossEnd, crossTensorEnd,
    LinearMap.comp_apply]

/-- Exponential transport for the `(X,Z)` left leg. -/
theorem exp_scaledLeftCross13
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledLeftCross13 p X Y Z) =
      (((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y) (crossExpEnd p X Z)) := by
  rw [scaledLeftCross13_eq_transport]
  let f := Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y
  let e := ((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm
  have hD := scaledCrossEnd_isNilpotent p X Z
  rw [← hD.map_exp f, ← (hD.map f).map_exp e]

/-- Exponential transport for the `(Y,Z)` left leg. -/
theorem exp_scaledLeftCross23
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledLeftCross23 p X Y Z) =
      (((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X) (crossExpEnd p Y Z)) := by
  rw [scaledLeftCross23_eq_transport]
  let f := Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X
  let e := ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm
  have hD := scaledCrossEnd_isNilpotent p Y Z
  rw [← hD.map_exp f, ← (hD.map f).map_exp e]

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

@[simp]
theorem leftExp13Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (leftExp13Hom p X Y Z).hom =
      IsNilpotent.exp (scaledLeftCross13 p X Y Z) := by
  rw [exp_scaledLeftCross13]
  apply LinearMap.ext
  intro t
  simp [leftExp13Hom, rightCommIso, LinearEquiv.conjAlgEquiv_apply,
    Module.End.rTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LinearMap.comp_apply]

@[simp]
theorem leftExp23Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (leftExp23Hom p X Y Z).hom =
      IsNilpotent.exp (scaledLeftCross23 p X Y Z) := by
  rw [exp_scaledLeftCross23]
  apply LinearMap.ext
  intro t
  simp [leftExp23Hom, LinearEquiv.conjAlgEquiv_apply,
    Module.End.lTensorAlgHom, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LogNilpotentModule.associatorIso,
    LogEndModule.associatorHom, LogEndModule.associatorInv,
    LinearMap.comp_apply]

/-- Categorical left-associated exponential splitting. -/
theorem crossExpHom_left_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpHom p (X ⊗ Y) Z =
      leftExp23Hom p X Y Z ≫ leftExp13Hom p X Y Z := by
  apply LogEndModule.Hom.ext
  change crossExpEnd p (X ⊗ Y) Z =
    (leftExp13Hom p X Y Z).hom.comp (leftExp23Hom p X Y Z).hom
  rw [leftExp13Hom_hom, leftExp23Hom_hom,
    ← Module.End.mul_eq_comp]
  exact crossExpEnd_left_factorization p X Y Z

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

/-! ## Tensoring the physical pair braiding -/

@[reassoc]
theorem physicalBraiding_tensor_right
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (physicalBraidingIso p X Y).hom ▷ Z =
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
theorem physicalBraiding_tensor_left
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Y ◁ (physicalBraidingIso p X Z).hom =
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

/-! ## Braided coherence -/

/-- Forward Mac Lane hexagon for the physical logarithmic braiding. -/
theorem physical_hexagon_forward
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).hom ≫
        (physicalBraidingIso p X (Y ⊗ Z)).hom ≫
        (α_ Y Z X).hom =
      ((physicalBraidingIso p X Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫
        (Y ◁ (physicalBraidingIso p X Z).hom) := by
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
  rw [physicalBraiding_tensor_right, physicalBraiding_tensor_left]

/-- Reverse Mac Lane hexagon for the physical logarithmic braiding. -/
theorem physical_hexagon_reverse
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).inv ≫
        (physicalBraidingIso p (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv =
      (X ◁ (physicalBraidingIso p Y Z).hom) ≫
        (α_ X Z Y).inv ≫
        ((physicalBraidingIso p X Z).hom ▷ Y) := by
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
  rw [physicalBraiding_tensor_left, physicalBraiding_tensor_right]

/-- One-variable naturality required by Mathlib's `BraidedCategory`, obtained
from the already-owned full two-variable naturality theorem. -/
theorem physical_braiding_naturality_right
    (p : ℂ) (X : LogNilpotentModule ℂ)
    {Y Z : LogNilpotentModule ℂ} (f : Y ⟶ Z) :
    X ◁ f ≫ (physicalBraidingIso p X Z).hom =
      (physicalBraidingIso p X Y).hom ≫ f ▷ X := by
  simpa using physicalBraiding_naturality p (𝟙 X) f

/-- Left-variable Mathlib naturality. -/
theorem physical_braiding_naturality_left
    (p : ℂ)
    {X Y : LogNilpotentModule ℂ} (f : X ⟶ Y)
    (Z : LogNilpotentModule ℂ) :
    f ▷ Z ≫ (physicalBraidingIso p Y Z).hom =
      (physicalBraidingIso p X Z).hom ≫ Z ◁ f := by
  simpa using physicalBraiding_naturality p f (𝟙 Z)

/-- Mathlib-native physical braided structure at arbitrary complex shear.

This is an explicit class value, not a global instance. -/
noncomputable def physicalBraidedCategory (p : ℂ) :
    BraidedCategory (LogNilpotentModule ℂ) where
  braiding := physicalBraidingIso p
  braiding_naturality_right := physical_braiding_naturality_right p
  braiding_naturality_left := physical_braiding_naturality_left p
  hexagon_forward := physical_hexagon_forward p
  hexagon_reverse := physical_hexagon_reverse p

/-- Physical Hadjiivanov specialization `p = -2πi`. -/
noncomputable def hadjiivanovBraidedCategory :
    BraidedCategory (LogNilpotentModule ℂ) :=
  physicalBraidedCategory logShearBase

/-- Readback under local activation of the physical Hadjiivanov braiding. -/
theorem hadjiivanov_braiding_hom
    (X Y : LogNilpotentModule ℂ) :
    letI : BraidedCategory (LogNilpotentModule ℂ) := hadjiivanovBraidedCategory
    (β_ X Y).hom = (physicalBraidingIso logShearBase X Y).hom := by
  rfl

end InfoGeometry.Categorical.LogNilpotentPhysicalBraidedCategory
