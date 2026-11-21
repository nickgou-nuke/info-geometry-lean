/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalCategory
open InfoGeometry.Categorical.LogNilpotentPhysicalBraiding
open InfoGeometry.Categorical.LogNilpotentPhysicalBraidingHexagon
open InfoGeometry.Clifford.LogCftMonodromy

/-- Restrict scalars along `ℚ → ℂ` on binary and ternary tensor carriers.  These
supply the `Module ℚ` instances required by Mathlib's finite nilpotent
exponential on the corresponding endomorphism algebras. -/
local instance ratModuleTensor (X Y : LogNilpotentModule ℂ) :
    Module ℚ (X.toLogEndModule.V ⊗[ℂ] Y.toLogEndModule.V) :=
  Module.compHom _ (algebraMap ℚ ℂ)

/-- The right-associated triple tensor. -/
local instance ratModuleTripleTensorRight (X Y Z : LogNilpotentModule ℂ) :
    Module ℚ
      (X.toLogEndModule.V ⊗[ℂ] (Y.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V)) :=
  Module.compHom _ (algebraMap ℚ ℂ)

/-- The left-associated triple tensor. -/
local instance ratModuleTripleTensorLeft (X Y Z : LogNilpotentModule ℂ) :
    Module ℚ
      ((X.toLogEndModule.V ⊗[ℂ] Y.toLogEndModule.V) ⊗[ℂ] Z.toLogEndModule.V) :=
  Module.compHom _ (algebraMap ℚ ℂ)

/-! ## Structural three-factor swaps -/

/-- Mathlib's `leftComm` lifted to the logarithmic category. -/
def leftCommIso (X Y Z : LogNilpotentModule ℂ) :
    X ⊗ (Y ⊗ Z) ≅ Y ⊗ (X ⊗ Z) where
  hom :=
    { hom := (TensorProduct.leftComm ℂ X Y Z).toLinearMap
      comm := by
        apply TensorProduct.ext_threefold'
        intro x y z
        change
          (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
              Z.toLogEndModule.V)
              (X.N x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z) +
                x ⊗ₜ[ℂ] (Y.N y ⊗ₜ[ℂ] z + y ⊗ₜ[ℂ] Z.N z)) =
            Y.N y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z) +
              y ⊗ₜ[ℂ] (X.N x ⊗ₜ[ℂ] z + x ⊗ₜ[ℂ] Z.N z)
        rw [TensorProduct.tmul_add, map_add, map_add]
        simp [TensorProduct.leftComm_tmul, TensorProduct.tmul_add, add_assoc,
          add_left_comm, add_comm] }
  inv :=
    { hom := (TensorProduct.leftComm ℂ X Y Z).symm.toLinearMap
      comm := by
        apply TensorProduct.ext_threefold'
        intro y x z
        change
          (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
              Z.toLogEndModule.V).symm
              (Y.N y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z) +
                y ⊗ₜ[ℂ] (X.N x ⊗ₜ[ℂ] z + x ⊗ₜ[ℂ] Z.N z)) =
            X.N x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z) +
              x ⊗ₜ[ℂ] (Y.N y ⊗ₜ[ℂ] z + y ⊗ₜ[ℂ] Z.N z)
        rw [TensorProduct.tmul_add, map_add, map_add]
        simp [TensorProduct.leftComm_symm_tmul, TensorProduct.tmul_add,
          add_assoc, add_left_comm, add_comm] }
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro w
    change
      (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
          Z.toLogEndModule.V).symm
        ((TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
            Z.toLogEndModule.V) w) = w
    exact (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
      Z.toLogEndModule.V).left_inv w
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro w
    change
      (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
          Z.toLogEndModule.V)
        ((TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
            Z.toLogEndModule.V).symm w) = w
    exact (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
      Z.toLogEndModule.V).right_inv w

/-- Mathlib's `rightComm` lifted to the logarithmic category. -/
def rightCommIso (X Y Z : LogNilpotentModule ℂ) :
    (X ⊗ Y) ⊗ Z ≅ (X ⊗ Z) ⊗ Y where
  hom :=
    { hom := (TensorProduct.rightComm ℂ X Y Z).toLinearMap
      comm := by
        apply TensorProduct.ext_threefold
        intro x y z
        change
          (TensorProduct.rightComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
              Z.toLogEndModule.V)
              ((X.N x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] Y.N y) ⊗ₜ[ℂ] z +
                (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] Z.N z) =
            (X.N x ⊗ₜ[ℂ] z + x ⊗ₜ[ℂ] Z.N z) ⊗ₜ[ℂ] y +
              (x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] Y.N y
        rw [TensorProduct.add_tmul, map_add, map_add]
        simp [TensorProduct.rightComm_tmul, TensorProduct.add_tmul,
          add_assoc, add_left_comm, add_comm] }
  inv :=
    { hom := (TensorProduct.rightComm ℂ X Y Z).symm.toLinearMap
      comm := by
        apply TensorProduct.ext_threefold
        intro x z y
        change
          (TensorProduct.rightComm ℂ X.toLogEndModule.V Z.toLogEndModule.V
              Y.toLogEndModule.V)
              ((X.N x ⊗ₜ[ℂ] z + x ⊗ₜ[ℂ] Z.N z) ⊗ₜ[ℂ] y +
                (x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] Y.N y) =
            (X.N x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] Y.N y) ⊗ₜ[ℂ] z +
              (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] Z.N z
        rw [TensorProduct.add_tmul, map_add, map_add]
        simp [TensorProduct.rightComm_tmul, TensorProduct.add_tmul,
          add_assoc, add_left_comm, add_comm] }
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro w
    change
      (TensorProduct.rightComm ℂ X.toLogEndModule.V Z.toLogEndModule.V
          Y.toLogEndModule.V)
        ((TensorProduct.rightComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
            Z.toLogEndModule.V) w) = w
    rw [← TensorProduct.rightComm_symm]
    exact (TensorProduct.rightComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
      Z.toLogEndModule.V).left_inv w
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro w
    change
      (TensorProduct.rightComm ℂ X.toLogEndModule.V Y.toLogEndModule.V
          Z.toLogEndModule.V)
        ((TensorProduct.rightComm ℂ X.toLogEndModule.V Z.toLogEndModule.V
            Y.toLogEndModule.V) w) = w
    rw [← TensorProduct.rightComm_symm]
    exact (TensorProduct.rightComm ℂ X.toLogEndModule.V Z.toLogEndModule.V
      Y.toLogEndModule.V).left_inv w

/-- `leftComm` is associator--swap--associator. -/
@[reassoc]
theorem assoc_leftComm
    (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).hom ≫ (leftCommIso X Y Z).hom =
      LogNilpotentModule.tensorHom
          (LogNilpotentModule.symmetricSwapIso X Y).hom (𝟙 Z) ≫
        (α_ Y X Z).hom := by
  apply LogEndModule.Hom.ext
  apply TensorProduct.ext_threefold
  intro x y z
  change
    (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V Z.toLogEndModule.V)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) =
      (TensorProduct.assoc ℂ Y.toLogEndModule.V X.toLogEndModule.V Z.toLogEndModule.V)
        (TensorProduct.map
          (TensorProduct.comm ℂ X.toLogEndModule.V Y.toLogEndModule.V).toLinearMap
          (LinearMap.id : Module.End ℂ Z.toLogEndModule.V)
          ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z))
  simp [TensorProduct.leftComm_tmul, TensorProduct.assoc_tmul, TensorProduct.comm_tmul]

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
  apply TensorProduct.ext_threefold'
  intro x y z
  change
    (TensorProduct.assoc ℂ Y.toLogEndModule.V Z.toLogEndModule.V X.toLogEndModule.V)
      (TensorProduct.comm ℂ X.toLogEndModule.V (Y.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z))) =
      TensorProduct.map (LinearMap.id : Module.End ℂ Y.toLogEndModule.V)
        (TensorProduct.comm ℂ X.toLogEndModule.V Z.toLogEndModule.V).toLinearMap
        ((TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V Z.toLogEndModule.V)
          (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)))
  simp [TensorProduct.leftComm_tmul, TensorProduct.assoc_tmul, TensorProduct.comm_tmul]

/-- Inverse associator followed by `rightComm` is the inner `Y,Z` swap followed
by the inverse associator. -/
@[reassoc]
theorem assocInv_rightComm
    (X Y Z : LogNilpotentModule ℂ) :
    (α_ X Y Z).inv ≫ (rightCommIso X Y Z).hom =
      LogNilpotentModule.tensorHom (𝟙 X)
          (LogNilpotentModule.symmetricSwapIso Y Z).hom ≫
        (α_ X Z Y).inv := by
  apply LogEndModule.Hom.ext
  apply TensorProduct.ext_threefold'
  intro x y z
  change
    (TensorProduct.rightComm ℂ X.toLogEndModule.V Y.toLogEndModule.V Z.toLogEndModule.V)
      ((TensorProduct.assoc ℂ X.toLogEndModule.V Y.toLogEndModule.V Z.toLogEndModule.V).symm
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z))) =
      (TensorProduct.assoc ℂ X.toLogEndModule.V Z.toLogEndModule.V Y.toLogEndModule.V).symm
        (TensorProduct.map (LinearMap.id : Module.End ℂ X.toLogEndModule.V)
          (TensorProduct.comm ℂ Y.toLogEndModule.V Z.toLogEndModule.V).toLinearMap
          (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)))
  simp [TensorProduct.rightComm_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.comm_tmul]

/-- Full swap in the reverse hexagon factors through `rightComm`. -/
theorem swap_assocInv_eq_rightComm_swap
    (X Y Z : LogNilpotentModule ℂ) :
    (LogNilpotentModule.symmetricSwapIso (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv =
      (rightCommIso X Y Z).hom ≫
        LogNilpotentModule.tensorHom
          (LogNilpotentModule.symmetricSwapIso X Z).hom (𝟙 Y) := by
  apply LogEndModule.Hom.ext
  apply TensorProduct.ext_threefold
  intro x y z
  change
    (TensorProduct.assoc ℂ Z.toLogEndModule.V X.toLogEndModule.V Y.toLogEndModule.V).symm
      (TensorProduct.comm ℂ (X.toLogEndModule.V ⊗[ℂ] Y.toLogEndModule.V) Z.toLogEndModule.V
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)) =
      TensorProduct.map
        (TensorProduct.comm ℂ X.toLogEndModule.V Z.toLogEndModule.V).toLinearMap
        (LinearMap.id : Module.End ℂ Y.toLogEndModule.V)
        ((TensorProduct.rightComm ℂ X.toLogEndModule.V Y.toLogEndModule.V Z.toLogEndModule.V)
          ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z))
  simp [TensorProduct.rightComm_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.comm_tmul]

/-! ## Right-associated exponential legs -/

/-- The existing first right-associated triple leg is the associator transport
of the pair cross generator. -/
theorem scaledLeftTripleCross_eq_transport
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledLeftTripleCross p X Y Z =
      ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z) (scaledCrossEnd p X Y)) := by
  apply TensorProduct.ext_threefold'
  intro x y z
  change
    p • (X.N x ⊗ₜ[ℂ] (Y.N y ⊗ₜ[ℂ] z)) =
      p • (TensorProduct.assoc ℂ X.toLogEndModule.V Y.toLogEndModule.V Z.toLogEndModule.V)
        (((Module.End.rTensorAlgHom ℂ
            (X.toLogEndModule.V ⊗[ℂ] Y.toLogEndModule.V) Z.toLogEndModule.V)
          (TensorProduct.map X.N Y.N)) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z))
  simp [Module.End.rTensorAlgHom, AlgHom.ofLinearMap_apply, LinearMap.rTensorHom,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul, TensorProduct.assoc_tmul]

/-- The second right-associated triple leg is the `leftComm` pullback of the
`(X,Z)` pair cross generator. -/
theorem scaledRightTripleCross_eq_transport
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledRightTripleCross p X Y Z =
      (((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y) (scaledCrossEnd p X Z)) := by
  apply TensorProduct.ext_threefold'
  intro x y z
  change
    p • (X.N x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] Z.N z)) =
      p • (TensorProduct.leftComm ℂ X.toLogEndModule.V Y.toLogEndModule.V Z.toLogEndModule.V).symm
        (((Module.End.lTensorAlgHom ℂ
            (X.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V) Y.toLogEndModule.V)
          (TensorProduct.map X.N Z.N)) (y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z)))
  simp [Module.End.lTensorAlgHom, AlgHom.ofLinearMap_apply, LinearMap.lTensorHom,
    LinearMap.lTensor_tmul, TensorProduct.map_tmul, TensorProduct.leftComm_symm_tmul]

/-- Exponential transport for the `(X,Y)` triple leg. -/
theorem exp_scaledLeftTripleCross
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledLeftTripleCross p X Y Z) =
      ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z) (crossExpEnd p X Y)) := by
  rw [scaledLeftTripleCross_eq_transport, crossExpEnd]
  obtain ⟨k, hk⟩ := scaledCrossEnd_isNilpotent p X Y
  let f := Module.End.rTensorAlgHom ℂ
    (X.toLogEndModule.V ⊗[ℂ] Y.toLogEndModule.V) Z.toLogEndModule.V
  let e := (TensorProduct.assoc ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V).conjAlgEquiv ℂ
  have hpow : (e (f (scaledCrossEnd p X Y))) ^ k = 0 := by
    simp [f, e, ← map_pow, hk]
  rw [IsNilpotent.exp_eq_sum hpow]
  rw [IsNilpotent.exp_eq_sum hk]
  simp [f, e, map_sum, map_rat_smul, map_pow]

/-- Exponential transport for the `(X,Z)` triple leg. -/
theorem exp_scaledRightTripleCross
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledRightTripleCross p X Y Z) =
      (((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y) (crossExpEnd p X Z)) := by
  rw [scaledRightTripleCross_eq_transport, crossExpEnd]
  obtain ⟨k, hk⟩ := scaledCrossEnd_isNilpotent p X Z
  let f := Module.End.lTensorAlgHom ℂ
    (X.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V) Y.toLogEndModule.V
  let e := ((TensorProduct.leftComm ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V).conjAlgEquiv ℂ).symm
  have hpow : (e (f (scaledCrossEnd p X Z))) ^ k = 0 := by
    simp [f, e, ← map_pow, hk]
  rw [IsNilpotent.exp_eq_sum hpow]
  rw [IsNilpotent.exp_eq_sum hk]
  simp [f, e, map_sum, map_rat_smul, map_pow]

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
  let assoc := TensorProduct.assoc ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V
  let D := crossExpEnd p X Y
  apply LinearMap.ext
  intro t
  change assoc.toLinearMap (D.rTensor Z.toLogEndModule.V (assoc.symm t)) =
    assoc.toLinearMap (D.rTensor Z.toLogEndModule.V (assoc.symm t))
  rfl

@[simp]
theorem rightExp13Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (rightExp13Hom p X Y Z).hom =
      IsNilpotent.exp (scaledRightTripleCross p X Y Z) := by
  rw [exp_scaledRightTripleCross]
  let lc := TensorProduct.leftComm ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V
  let D := crossExpEnd p X Z
  apply LinearMap.ext
  intro t
  change lc.symm (D.lTensor Y.toLogEndModule.V (lc t)) =
    lc.symm (D.lTensor Y.toLogEndModule.V (lc t))
  rfl

/-- Categorical right-associated exponential splitting. -/
theorem crossExpHom_right_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpHom p X (Y ⊗ Z) =
      rightExp12Hom p X Y Z ≫ rightExp13Hom p X Y Z := by
  apply LogEndModule.Hom.ext
  cases LogNilpotentModule.tensorObj_carrier Y Z
  simp [crossExpHom, rightExp12Hom_hom, rightExp13Hom_hom,
    Module.End.mul_eq_comp, crossExpEnd_tensorObj_factorization_rev p X Y Z]
  rfl

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

section
-- In this section `⊗` is read as the raw `ℂ`-tensor product of carriers, so the
-- endomorphism carriers below elaborate without ambiguous tensor-notation
-- metavariables.
local notation:100 M:100 " ⊗ " N:101 => TensorProduct ℂ M N

/-- `p N_X ⊗ id_Y ⊗ N_Z` on `(X ⊗ Y) ⊗ Z`. -/
def scaledLeftCross13
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ ((X ⊗ Y) ⊗ Z) :=
  p • TensorProduct.map
    (TensorProduct.map X.N (LinearMap.id : Module.End ℂ Y.toLogEndModule.V))
    Z.N

/-- `p id_X ⊗ N_Y ⊗ N_Z` on `(X ⊗ Y) ⊗ Z`. -/
def scaledLeftCross23
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ ((X ⊗ Y) ⊗ Z) :=
  p • TensorProduct.map
    (TensorProduct.map (LinearMap.id : Module.End ℂ X.toLogEndModule.V) Y.N)
    Z.N

end

/-- The cross generator for `(X ⊗ Y,Z)` splits into the two left-associated
legs. -/
theorem scaledCrossEnd_left_eq_add
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledCrossEnd p (X ⊗ Y) Z =
      scaledLeftCross13 p X Y Z + scaledLeftCross23 p X Y Z := by
  change scaledCrossEnd p (LogNilpotentModule.tensorObj X Y) Z =
    scaledLeftCross13 p X Y Z + scaledLeftCross23 p X Y Z
  cases LogNilpotentModule.tensorObj_carrier X Y
  apply TensorProduct.ext_threefold
  intro x y z
  simp only [scaledCrossEnd, crossTensorEnd, scaledLeftCross13, scaledLeftCross23,
    LogNilpotentModule.tensorObj, LogEndModule.tensorObj]
  change p • (TensorProduct.map
      (TensorProduct.map X.toLogEndModule.N (LinearMap.id : Module.End ℂ Y.toLogEndModule.V) +
       TensorProduct.map (LinearMap.id : Module.End ℂ X.toLogEndModule.V) Y.toLogEndModule.N)
      Z.toLogEndModule.N) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
    (p • TensorProduct.map
      (TensorProduct.map X.toLogEndModule.N (LinearMap.id : Module.End ℂ Y.toLogEndModule.V))
      Z.toLogEndModule.N) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) +
    (p • TensorProduct.map
      (TensorProduct.map (LinearMap.id : Module.End ℂ X.toLogEndModule.V) Y.toLogEndModule.N)
      Z.toLogEndModule.N) ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)
  simp [TensorProduct.map_tmul, TensorProduct.add_tmul, smul_add]

/-- The two left-associated legs commute. -/
theorem scaledLeftCross_commute
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Commute (scaledLeftCross13 p X Y Z) (scaledLeftCross23 p X Y Z) := by
  apply Commute.eq
  apply TensorProduct.ext_threefold
  intro x y z
  simp [scaledLeftCross13, scaledLeftCross23,
    Module.End.mul_eq_comp, LinearMap.comp_apply, TensorProduct.map_tmul,
    smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The `(X,Z)` left-associated leg is nilpotent. -/
theorem scaledLeftCross13_isNilpotent
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (scaledLeftCross13 p X Y Z) := by
  refine ⟨X.nilpotencyOrder, ?_⟩
  rw [scaledLeftCross13]
  have hp : ∀ n,
      (p • TensorProduct.map
        (TensorProduct.map X.N (LinearMap.id : Module.End ℂ Y.toLogEndModule.V))
        Z.N) ^ n =
      p ^ n • TensorProduct.map
        (TensorProduct.map (X.N ^ n) (LinearMap.id : Module.End ℂ Y.toLogEndModule.V))
        (Z.N ^ n) := by
    intro n
    induction n with
    | zero => ext x y z <;> simp
    | succ n ih =>
        rw [pow_succ, ih, pow_succ, pow_succ]
        ext x y z
        simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
          TensorProduct.map_tmul, smul_smul, pow_succ, mul_comm]
  rw [hp, X.nilpotent]
  simp

/-- The `(Y,Z)` left-associated leg is nilpotent. -/
theorem scaledLeftCross23_isNilpotent
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (scaledLeftCross23 p X Y Z) := by
  refine ⟨Y.nilpotencyOrder, ?_⟩
  rw [scaledLeftCross23]
  have hp : ∀ n,
      (p • TensorProduct.map
        (TensorProduct.map (LinearMap.id : Module.End ℂ X.toLogEndModule.V) Y.N)
        Z.N) ^ n =
      p ^ n • TensorProduct.map
        (TensorProduct.map (LinearMap.id : Module.End ℂ X.toLogEndModule.V) (Y.N ^ n))
        (Z.N ^ n) := by
    intro n
    induction n with
    | zero => ext x y z <;> simp
    | succ n ih =>
        rw [pow_succ, ih, pow_succ, pow_succ]
        ext x y z
        simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
          TensorProduct.map_tmul, smul_smul, pow_succ, mul_comm]
  rw [hp, Y.nilpotent]
  simp

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
  rw [scaledLeftCross13]
  rw [LinearEquiv.symm_conjAlgEquiv, LinearEquiv.conjAlgEquiv_apply]
  apply TensorProduct.ext_threefold
  intro x y z
  simp [scaledCrossEnd, crossTensorEnd, Module.End.rTensorAlgHom,
    AlgHom.ofLinearMap_apply, LinearMap.rTensorHom, LinearMap.rTensor_tmul,
    TensorProduct.map_tmul, TensorProduct.rightComm_tmul,
    TensorProduct.rightComm_symm]

/-- The `(Y,Z)` left leg is the inverse-associator pullback of the pair
generator. -/
theorem scaledLeftCross23_eq_transport
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledLeftCross23 p X Y Z =
      (((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X) (scaledCrossEnd p Y Z)) := by
  rw [scaledLeftCross23]
  rw [LinearEquiv.symm_conjAlgEquiv, LinearEquiv.conjAlgEquiv_apply]
  apply TensorProduct.ext_threefold
  intro x y z
  simp [scaledCrossEnd, crossTensorEnd, Module.End.lTensorAlgHom,
    AlgHom.ofLinearMap_apply, LinearMap.lTensorHom, LinearMap.lTensor_tmul,
    TensorProduct.map_tmul, TensorProduct.assoc_symm_tmul]

/-- Exponential transport for the `(X,Z)` left leg. -/
theorem exp_scaledLeftCross13
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledLeftCross13 p X Y Z) =
      (((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y) (crossExpEnd p X Z)) := by
  rw [scaledLeftCross13_eq_transport, crossExpEnd]
  obtain ⟨k, hk⟩ := scaledCrossEnd_isNilpotent p X Z
  let f := Module.End.rTensorAlgHom ℂ
    (X.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V) Y.toLogEndModule.V
  let e := ((TensorProduct.rightComm ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V).conjAlgEquiv ℂ).symm
  have hpow : (e (f (scaledCrossEnd p X Z))) ^ k = 0 := by
    simp [f, e, ← map_pow, hk]
  rw [IsNilpotent.exp_eq_sum hpow]
  rw [IsNilpotent.exp_eq_sum hk]
  simp [f, e, map_sum, map_rat_smul, map_pow]

/-- Exponential transport for the `(Y,Z)` left leg. -/
theorem exp_scaledLeftCross23
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (scaledLeftCross23 p X Y Z) =
      (((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X) (crossExpEnd p Y Z)) := by
  rw [scaledLeftCross23_eq_transport, crossExpEnd]
  obtain ⟨k, hk⟩ := scaledCrossEnd_isNilpotent p Y Z
  let f := Module.End.lTensorAlgHom ℂ
    (Y.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V) X.toLogEndModule.V
  let e := ((TensorProduct.assoc ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V).conjAlgEquiv ℂ).symm
  have hpow : (e (f (scaledCrossEnd p Y Z))) ^ k = 0 := by
    simp [f, e, ← map_pow, hk]
  rw [IsNilpotent.exp_eq_sum hpow]
  rw [IsNilpotent.exp_eq_sum hk]
  simp [f, e, map_sum, map_rat_smul, map_pow]

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
  rw [exp_scaledLeftCross13, LinearEquiv.symm_conjAlgEquiv,
    LinearEquiv.conjAlgEquiv_apply]
  let rc := TensorProduct.rightComm ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V
  let D := crossExpEnd p X Z
  apply LinearMap.ext
  intro t
  change rc.symm (D.rTensor Y.toLogEndModule.V (rc t)) =
    rc.symm (D.rTensor Y.toLogEndModule.V (rc t))
  rfl

@[simp]
theorem leftExp23Hom_hom
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    (leftExp23Hom p X Y Z).hom =
      IsNilpotent.exp (scaledLeftCross23 p X Y Z) := by
  rw [exp_scaledLeftCross23, LinearEquiv.symm_conjAlgEquiv,
    LinearEquiv.conjAlgEquiv_apply]
  let assoc := TensorProduct.assoc ℂ X.toLogEndModule.V
    Y.toLogEndModule.V Z.toLogEndModule.V
  let D := crossExpEnd p Y Z
  apply LinearMap.ext
  intro t
  change assoc.symm (D.lTensor X.toLogEndModule.V (assoc t)) =
    assoc.symm (D.lTensor X.toLogEndModule.V (assoc t))
  rfl

/-- Categorical left-associated exponential splitting. -/
theorem crossExpHom_left_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpHom p (X ⊗ Y) Z =
      leftExp23Hom p X Y Z ≫ leftExp13Hom p X Y Z := by
  apply LogEndModule.Hom.ext
  change crossExpEnd p (X ⊗ Y) Z =
    (leftExp13Hom p X Y Z).hom.comp (leftExp23Hom p X Y Z).hom
  rw [leftExp13Hom_hom, leftExp23Hom_hom]
  change crossExpEnd p (X ⊗ Y) Z =
    IsNilpotent.exp (scaledLeftCross13 p X Y Z) *
      IsNilpotent.exp (scaledLeftCross23 p X Y Z)
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
  rw [assoc_rightExp12_assoc]
  rw [swap_assoc_eq_leftComm_swap]
  rw [rightExp13_leftComm_assoc]
  rw [assoc_leftComm_assoc]
  rw [physicalBraiding_tensor_right, physicalBraiding_tensor_left]
  simp only [Category.assoc]

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
  rw [assocInv_leftExp23_assoc]
  rw [swap_assocInv_eq_rightComm_swap]
  rw [leftExp13_rightComm_assoc]
  rw [assocInv_rightComm_assoc]
  rw [physicalBraiding_tensor_left, physicalBraiding_tensor_right]
  simp only [Category.assoc]

/-- One-variable naturality required by Mathlib's `BraidedCategory`, obtained
from the already-owned full two-variable naturality theorem. -/
theorem physical_braiding_naturality_right
    (p : ℂ) (X : LogNilpotentModule ℂ)
    {Y Z : LogNilpotentModule ℂ} (f : Y ⟶ Z) :
    X ◁ f ≫ (physicalBraidingIso p X Z).hom =
      (physicalBraidingIso p X Y).hom ≫ f ▷ X := by
  change LogNilpotentModule.tensorHom (𝟙 X) f ≫ (physicalBraidingIso p X Z).hom =
    (physicalBraidingIso p X Y).hom ≫ LogNilpotentModule.tensorHom f (𝟙 X)
  exact physicalBraiding_naturality p (𝟙 X) f

/-- Left-variable Mathlib naturality. -/
theorem physical_braiding_naturality_left
    (p : ℂ)
    {X Y : LogNilpotentModule ℂ} (f : X ⟶ Y)
    (Z : LogNilpotentModule ℂ) :
    f ▷ Z ≫ (physicalBraidingIso p Y Z).hom =
      (physicalBraidingIso p X Z).hom ≫ Z ◁ f := by
  change LogNilpotentModule.tensorHom f (𝟙 Z) ≫ (physicalBraidingIso p Y Z).hom =
    (physicalBraidingIso p X Z).hom ≫ LogNilpotentModule.tensorHom (𝟙 Z) f
  exact physicalBraiding_naturality p f (𝟙 Z)

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
