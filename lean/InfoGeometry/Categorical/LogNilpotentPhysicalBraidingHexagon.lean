/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.LogNilpotentPhysicalBraiding

/-!
# InfoGeometry.Categorical.LogNilpotentPhysicalBraidingHexagon

Tensor-leg exponential factorization underlying the physical logarithmic
braiding hexagons.

On the right-associated triple tensor `X ⊗ (Y ⊗ Z)` the cross generator for
`X` against the tensor product `Y ⊗ Z` splits as

`p N_X ⊗ N_(Y⊗Z) = A + B`,

where

* `A = p N_X ⊗ N_Y ⊗ id`,
* `B = p N_X ⊗ id ⊗ N_Z`.

The two endomorphisms commute and are nilpotent.  Hence Mathlib's
`IsNilpotent.exp_add_of_commute` gives the exact finite factorization

`exp(p N_X ⊗ N_(Y⊗Z)) = exp(A) * exp(B)`.

This is the algebraic content of the forward braided hexagon.  The dual
left-associated statement is obtained by the same construction after applying
the associator and is used by the categorical packaging node.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentPhysicalBraidingHexagon

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentPhysicalBraiding

/-- Restrict scalars along `ℚ → ℂ` on the right-associated triple tensor.  This
supplies the `Module ℚ` instance required by Mathlib's finite nilpotent
exponential on the endomorphism algebra of that tensor. -/
local instance ratModuleTensorProduct (X Y : LogNilpotentModule ℂ) :
    Module ℚ (X.toLogEndModule.V ⊗[ℂ] Y.toLogEndModule.V) :=
  Module.compHom _ (algebraMap ℚ ℂ)

/-- The raw right-associated triple tensor is also the tensor of `X` with the
bundled tensor object `tensorObj Y Z`; this instance covers its unrolled form. -/
local instance ratModuleTripleTensor (X Y Z : LogNilpotentModule ℂ) :
    Module ℚ
      (X.toLogEndModule.V ⊗[ℂ] (Y.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V)) :=
  Module.compHom _ (algebraMap ℚ ℂ)

/-- Unfold the cross generator against the bundled tensor object into a map on
the raw right-associated triple tensor. -/
theorem crossTensorEnd_tensorObj_eq (X Y Z : LogNilpotentModule ℂ) :
    crossTensorEnd X.toLogEndModule (Y.tensorObj Z).toLogEndModule =
      (TensorProduct.map X.N
        (TensorProduct.map Y.N (LinearMap.id : Module.End ℂ Z) +
          TensorProduct.map (LinearMap.id : Module.End ℂ Y) Z.N) :
        Module.End ℂ (X.toLogEndModule.V ⊗[ℂ]
          (Y.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V))) :=
  rfl

/-- Unscaled `N_X ⊗ N_Y ⊗ id_Z` on the right-associated triple tensor. -/
def leftTripleCross
    (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗[ℂ] (Y ⊗[ℂ] Z)) :=
  TensorProduct.map X.N
    (TensorProduct.map Y.N (LinearMap.id : Module.End ℂ Z))

/-- Unscaled `N_X ⊗ id_Y ⊗ N_Z` on the right-associated triple tensor. -/
def rightTripleCross
    (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗[ℂ] (Y ⊗[ℂ] Z)) :=
  TensorProduct.map X.N
    (TensorProduct.map (LinearMap.id : Module.End ℂ Y) Z.N)

/-- Scaled left tensor-leg cross generator. -/
def scaledLeftTripleCross
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗[ℂ] (Y ⊗[ℂ] Z)) :=
  p • leftTripleCross X Y Z

/-- Scaled right tensor-leg cross generator. -/
def scaledRightTripleCross
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗[ℂ] (Y ⊗[ℂ] Z)) :=
  p • rightTripleCross X Y Z

/-- Action of the scaled left triple-leg generator on a pure tensor. -/
theorem scaledLeftTripleCross_apply_tmul
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ)
    (x : X.toLogEndModule.V) (yz : Y.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V) :
    scaledLeftTripleCross p X Y Z (x ⊗ₜ[ℂ] yz) =
      p • (X.N x ⊗ₜ[ℂ]
        ((TensorProduct.map Y.N (LinearMap.id : Module.End ℂ Z)) yz)) := by
  change (p • TensorProduct.map X.N
      (TensorProduct.map Y.N (LinearMap.id : Module.End ℂ Z))) (x ⊗ₜ[ℂ] yz) = _
  rw [LinearMap.smul_apply, TensorProduct.map_tmul]

/-- Action of the scaled right triple-leg generator on a pure tensor. -/
theorem scaledRightTripleCross_apply_tmul
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ)
    (x : X.toLogEndModule.V) (yz : Y.toLogEndModule.V ⊗[ℂ] Z.toLogEndModule.V) :
    scaledRightTripleCross p X Y Z (x ⊗ₜ[ℂ] yz) =
      p • (X.N x ⊗ₜ[ℂ]
        ((TensorProduct.map (LinearMap.id : Module.End ℂ Y) Z.N) yz)) := by
  change (p • TensorProduct.map X.N
      (TensorProduct.map (LinearMap.id : Module.End ℂ Y) Z.N)) (x ⊗ₜ[ℂ] yz) = _
  rw [LinearMap.smul_apply, TensorProduct.map_tmul]

/-- Powers remain separated on the three tensor legs. -/
theorem leftTripleCross_pow
    (X Y Z : LogNilpotentModule ℂ) (n : ℕ) :
    (leftTripleCross X Y Z) ^ n =
      TensorProduct.map (X.N ^ n)
        (TensorProduct.map (Y.N ^ n)
          (LinearMap.id : Module.End ℂ Z)) := by
  induction n with
  | zero =>
      ext x y z
      simp [leftTripleCross]
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, pow_succ]
      ext x y z
      simp [leftTripleCross, Module.End.mul_eq_comp,
        LinearMap.comp_apply, TensorProduct.map_tmul]

/-- Powers of the second triple-leg cross generator. -/
theorem rightTripleCross_pow
    (X Y Z : LogNilpotentModule ℂ) (n : ℕ) :
    (rightTripleCross X Y Z) ^ n =
      TensorProduct.map (X.N ^ n)
        (TensorProduct.map (LinearMap.id : Module.End ℂ Y)
          (Z.N ^ n)) := by
  induction n with
  | zero =>
      ext x y z
      simp [rightTripleCross]
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, pow_succ]
      ext x y z
      simp [rightTripleCross, Module.End.mul_eq_comp,
        LinearMap.comp_apply, TensorProduct.map_tmul]

/-- Left triple-leg generator is nilpotent. -/
theorem leftTripleCross_isNilpotent
    (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (leftTripleCross X Y Z) := by
  refine ⟨X.nilpotencyOrder, ?_⟩
  rw [leftTripleCross_pow, X.nilpotent]
  ext x y z
  simp

/-- Right triple-leg generator is nilpotent. -/
theorem rightTripleCross_isNilpotent
    (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (rightTripleCross X Y Z) := by
  refine ⟨X.nilpotencyOrder, ?_⟩
  rw [rightTripleCross_pow, X.nilpotent]
  ext x y z
  simp

/-- Scaled left triple-leg generator remains nilpotent. -/
theorem scaledLeftTripleCross_isNilpotent
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (scaledLeftTripleCross p X Y Z) :=
  (leftTripleCross_isNilpotent X Y Z).smul p

/-- Scaled right triple-leg generator remains nilpotent. -/
theorem scaledRightTripleCross_isNilpotent
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (scaledRightTripleCross p X Y Z) :=
  (rightTripleCross_isNilpotent X Y Z).smul p

/-- The two tensor-leg cross generators commute. -/
theorem scaledTripleCross_commute
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    Commute
      (scaledLeftTripleCross p X Y Z)
      (scaledRightTripleCross p X Y Z) := by
  apply Commute.eq
  ext x y z
  simp [scaledLeftTripleCross, scaledRightTripleCross,
    leftTripleCross, rightTripleCross, Module.End.mul_eq_comp,
    LinearMap.comp_apply, TensorProduct.map_tmul, smul_smul,
    mul_comm, mul_left_comm, mul_assoc]

/-- The cross generator against the primitive tensor logarithm splits into the
two commuting tensor-leg generators. -/
theorem scaledCrossEnd_tensorObj_eq_add
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    scaledCrossEnd p X (LogNilpotentModule.tensorObj Y Z) =
      scaledLeftTripleCross p X Y Z + scaledRightTripleCross p X Y Z := by
  have hraw :
      p • (TensorProduct.map X.N
              (TensorProduct.map Y.N (LinearMap.id : Module.End ℂ Z)) +
             TensorProduct.map X.N
              (TensorProduct.map (LinearMap.id : Module.End ℂ Y) Z.N)) =
        scaledLeftTripleCross p X Y Z + scaledRightTripleCross p X Y Z := by
    apply TensorProduct.ext'
    intro x y
    induction y using TensorProduct.induction_on with
    | zero =>
        simp [scaledLeftTripleCross, scaledRightTripleCross,
          leftTripleCross, rightTripleCross]
    | tmul y' z' =>
        rw [LinearMap.smul_apply, LinearMap.add_apply]
        rw [LinearMap.add_apply]
        rw [scaledLeftTripleCross_apply_tmul p X Y Z x (y' ⊗ₜ[ℂ] z')]
        rw [scaledRightTripleCross_apply_tmul p X Y Z x (y' ⊗ₜ[ℂ] z')]
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
          TensorProduct.map_tmul, TensorProduct.map_tmul]
        rw [smul_add]
    | add y₁ y₂ h₁ h₂ =>
        rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂]
  change p • crossTensorEnd X.toLogEndModule (Y.tensorObj Z).toLogEndModule =
    scaledLeftTripleCross p X Y Z + scaledRightTripleCross p X Y Z
  rw [crossTensorEnd_tensorObj_eq X Y Z, TensorProduct.map_add_right]
  exact hraw

/-- Exact finite exponential factorization on the right-associated triple
tensor.  This is the algebraic core of the forward braiding hexagon. -/
theorem crossExpEnd_tensorObj_factorization
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpEnd p X (LogNilpotentModule.tensorObj Y Z) =
      IsNilpotent.exp (scaledLeftTripleCross p X Y Z) *
        IsNilpotent.exp (scaledRightTripleCross p X Y Z) := by
  rw [crossExpEnd, scaledCrossEnd_tensorObj_eq_add]
  exact IsNilpotent.exp_add_of_commute
    (scaledTripleCross_commute p X Y Z)
    (scaledLeftTripleCross_isNilpotent p X Y Z)
    (scaledRightTripleCross_isNilpotent p X Y Z)

end InfoGeometry.Categorical.LogNilpotentPhysicalBraidingHexagon
