/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.RingTheory.Nilpotent.Exp
import InfoGeometry.Categorical.LogNilpotentAmbientSymmetric

/-!
# InfoGeometry.Categorical.LogNilpotentPhysicalBraiding

Algebraic two-object logarithmic exchange family on the tensor-closed category
of finite-nilpotent logarithmic modules.

For objects `X,Y` and parameter `p : ℂ`, set

`D_{X,Y} = p • (N_X ⊗ N_Y)`

and use Mathlib's finite nilpotent exponential.  The candidate physical
exchange is

`c_{X,Y}(p) = τ_{X,Y} ∘ exp(D_{X,Y})`.

This is the correct tensor-closed extension of the rank-two formula
`τ ∘ (I + p N⊗N)`: when `N² = 0`, Mathlib's nilpotent exponential truncates
at first order, while for higher Jordan depth it retains exactly the finite
number of powers required by nilpotence.

This file proves the foundational statements needed before installing a
`BraidedCategory` value:

* `N_X ⊗ N_Y` is nilpotent for arbitrary finite-nilpotent `X,Y`;
* its scaled finite exponential is an automorphism in the logarithmic category;
* the exponential is natural for arbitrary logarithmic intertwiners;
* composing it with the ambient tensor swap gives a natural two-object family.

The two hexagon identities are deliberately left to the next DAG node, where
they can be proved from `IsNilpotent.exp_add_of_commute` after transporting the
three tensor-leg exponents through the associator.  No `BraidedCategory`
instance is installed here.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentPhysicalBraiding

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalCategory

/-- Powers of the mixed logarithmic tensor endomorphism are the tensor products
of the corresponding powers. -/
theorem crossTensorEnd_pow
    (X Y : LogNilpotentModule ℂ) (n : ℕ) :
    (crossTensorEnd X.toLogEndModule Y.toLogEndModule) ^ n =
      TensorProduct.map (X.N ^ n) (Y.N ^ n) := by
  induction n with
  | zero =>
      ext x y
      simp [crossTensorEnd]
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, pow_succ]
      ext x y
      simp [crossTensorEnd, Module.End.mul_eq_comp,
        LinearMap.comp_apply, TensorProduct.map_tmul]

/-- The cross term is nilpotent, with the nilpotency order of either factor
already giving a valid bound. -/
theorem crossTensorEnd_pow_order_eq_zero
    (X Y : LogNilpotentModule ℂ) :
    (crossTensorEnd X.toLogEndModule Y.toLogEndModule) ^
        X.nilpotencyOrder = 0 := by
  rw [crossTensorEnd_pow, X.nilpotent]
  ext x y
  simp

/-- `N_X ⊗ N_Y` is nilpotent for arbitrary objects of the tensor-closed
logarithmic category. -/
theorem crossTensorEnd_isNilpotent
    (X Y : LogNilpotentModule ℂ) :
    IsNilpotent (crossTensorEnd X.toLogEndModule Y.toLogEndModule) :=
  ⟨X.nilpotencyOrder, crossTensorEnd_pow_order_eq_zero X Y⟩

/-- Scaled cross logarithmic generator. -/
def scaledCrossEnd (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗[ℂ] Y) :=
  p • crossTensorEnd X.toLogEndModule Y.toLogEndModule

/-- Scaling preserves nilpotence. -/
theorem scaledCrossEnd_isNilpotent
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    IsNilpotent (scaledCrossEnd p X Y) :=
  (crossTensorEnd_isNilpotent X Y).smul p

end InfoGeometry.Categorical.LogNilpotentPhysicalBraiding
