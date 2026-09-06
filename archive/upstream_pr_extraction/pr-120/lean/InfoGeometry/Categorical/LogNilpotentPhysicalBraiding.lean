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

/-- The mixed cross term commutes with the primitive logarithmic tensor
endomorphism for arbitrary nilpotency depth. -/
theorem crossTensorEnd_commute_tensorN
    (X Y : LogNilpotentModule ℂ) :
    Commute
      (crossTensorEnd X.toLogEndModule Y.toLogEndModule)
      (LogNilpotentModule.tensorObj X Y).N := by
  apply Commute.eq
  ext x y
  simp [crossTensorEnd, LogEndModule.tensorObj_N_tmul,
    Module.End.mul_eq_comp, LinearMap.comp_apply, TensorProduct.map_tmul,
    add_comm, add_left_comm, add_assoc]

/-- The scaled cross term still commutes with the primitive tensor logarithm. -/
theorem scaledCrossEnd_commute_tensorN
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    Commute (scaledCrossEnd p X Y) (LogNilpotentModule.tensorObj X Y).N := by
  apply Commute.eq
  ext x y
  simp [scaledCrossEnd, crossTensorEnd, LogEndModule.tensorObj_N_tmul,
    Module.End.mul_eq_comp, LinearMap.comp_apply, TensorProduct.map_tmul,
    add_comm, add_left_comm, add_assoc]

/-- Mathlib's finite nilpotent exponential of the cross generator. -/
def crossExpEnd (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗[ℂ] Y) :=
  IsNilpotent.exp (scaledCrossEnd p X Y)

/-- The finite nilpotent exponential intertwines the primitive logarithmic
endomorphism. -/
theorem crossExpEnd_commutes_tensorN
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    (crossExpEnd p X Y).comp (LogNilpotentModule.tensorObj X Y).N =
      (LogNilpotentModule.tensorObj X Y).N.comp (crossExpEnd p X Y) := by
  have hD := scaledCrossEnd_isNilpotent p X Y
  have hcomm :
      (scaledCrossEnd p X Y).comp (LogNilpotentModule.tensorObj X Y).N =
        (LogNilpotentModule.tensorObj X Y).N.comp (scaledCrossEnd p X Y) := by
    simpa [Module.End.mul_eq_comp] using
      (scaledCrossEnd_commute_tensorN p X Y).eq
  simpa [crossExpEnd] using
    (Module.End.commute_exp_left_of_commute hD hD hcomm)

/-- The finite cross exponential as a logarithmic endomorphism. -/
def crossExpHom (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    LogNilpotentModule.tensorObj X Y ⟶ LogNilpotentModule.tensorObj X Y where
  hom := crossExpEnd p X Y
  comm := crossExpEnd_commutes_tensorN p X Y

/-- Exact inverse law for the finite cross exponential. -/
theorem crossExpHom_comp_neg
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    crossExpHom p X Y ≫ crossExpHom (-p) X Y =
      𝟙 (LogNilpotentModule.tensorObj X Y) := by
  apply LogEndModule.Hom.ext
  change
    (crossExpEnd (-p) X Y).comp (crossExpEnd p X Y) = LinearMap.id
  have hD := scaledCrossEnd_isNilpotent p X Y
  have hneg : scaledCrossEnd (-p) X Y = -(scaledCrossEnd p X Y) := by
    simp [scaledCrossEnd]
  rw [crossExpEnd, crossExpEnd, hneg]
  simpa [Module.End.mul_eq_comp] using
    (IsNilpotent.exp_neg_mul_exp_self hD)

/-- Reverse exact inverse law. -/
theorem crossExpHom_neg_comp
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    crossExpHom (-p) X Y ≫ crossExpHom p X Y =
      𝟙 (LogNilpotentModule.tensorObj X Y) := by
  apply LogEndModule.Hom.ext
  change
    (crossExpEnd p X Y).comp (crossExpEnd (-p) X Y) = LinearMap.id
  have hD := scaledCrossEnd_isNilpotent p X Y
  have hneg : scaledCrossEnd (-p) X Y = -(scaledCrossEnd p X Y) := by
    simp [scaledCrossEnd]
  rw [crossExpEnd, crossExpEnd, hneg]
  simpa [Module.End.mul_eq_comp] using
    (IsNilpotent.exp_mul_exp_neg_self hD)

/-- The finite cross exponential is an automorphism in the logarithmic
category. -/
def crossExpIso (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    LogNilpotentModule.tensorObj X Y ≅ LogNilpotentModule.tensorObj X Y where
  hom := crossExpHom p X Y
  inv := crossExpHom (-p) X Y
  hom_inv_id := crossExpHom_comp_neg p X Y
  inv_hom_id := crossExpHom_neg_comp p X Y

/-- The cross generator is natural with respect to arbitrary logarithmic
intertwiners. -/
theorem scaledCrossEnd_intertwines
    (p : ℂ)
    {X X' Y Y' : LogNilpotentModule ℂ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (scaledCrossEnd p X' Y').comp
        (LogNilpotentModule.tensorHom f g).hom =
      (LogNilpotentModule.tensorHom f g).hom.comp
        (scaledCrossEnd p X Y) := by
  ext x y
  simp [scaledCrossEnd, crossTensorEnd, LogNilpotentModule.tensorHom,
    LogEndModule.tensorHom, LinearMap.comp_apply, TensorProduct.map_tmul,
    f.map_N, g.map_N]

/-- Naturality of the finite nilpotent exponential follows directly from
Mathlib's polynomial-exponential intertwining theorem. -/
theorem crossExp_naturality
    (p : ℂ)
    {X X' Y Y' : LogNilpotentModule ℂ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    LogNilpotentModule.tensorHom f g ≫ crossExpHom p X' Y' =
      crossExpHom p X Y ≫ LogNilpotentModule.tensorHom f g := by
  apply LogEndModule.Hom.ext
  change
    (crossExpEnd p X' Y').comp
        (LogNilpotentModule.tensorHom f g).hom =
      (LogNilpotentModule.tensorHom f g).hom.comp (crossExpEnd p X Y)
  simpa [crossExpEnd] using
    (Module.End.commute_exp_left_of_commute
      (scaledCrossEnd_isNilpotent p X Y)
      (scaledCrossEnd_isNilpotent p X' Y')
      (scaledCrossEnd_intertwines p f g))

/-- Two-object physical logarithmic exchange candidate:
`τ_{X,Y} ∘ exp(p N_X⊗N_Y)`. -/
def physicalBraidingIso
    (p : ℂ) (X Y : LogNilpotentModule ℂ) :
    LogNilpotentModule.tensorObj X Y ≅ LogNilpotentModule.tensorObj Y X :=
  (crossExpIso p X Y).trans (LogNilpotentModule.symmetricSwapIso X Y)

/-- Naturality of the ambient tensor swap, stated here in two-variable form for
composition with the physical exponential. -/
theorem symmetricSwap_naturality
    {X X' Y Y' : LogNilpotentModule ℂ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    LogNilpotentModule.tensorHom f g ≫
        (LogNilpotentModule.symmetricSwapIso X' Y').hom =
      (LogNilpotentModule.symmetricSwapIso X Y).hom ≫
        LogNilpotentModule.tensorHom g f := by
  apply LogEndModule.Hom.ext
  ext x y
  simp [LogNilpotentModule.tensorHom, LogEndModule.tensorHom,
    LogNilpotentModule.symmetricSwapIso, LogEndModule.braidingHom,
    LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul]

/-- Full two-object naturality of the physical logarithmic exchange family. -/
theorem physicalBraiding_naturality
    (p : ℂ)
    {X X' Y Y' : LogNilpotentModule ℂ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    LogNilpotentModule.tensorHom f g ≫ (physicalBraidingIso p X' Y').hom =
      (physicalBraidingIso p X Y).hom ≫ LogNilpotentModule.tensorHom g f := by
  change
    LogNilpotentModule.tensorHom f g ≫
        crossExpHom p X' Y' ≫
        (LogNilpotentModule.symmetricSwapIso X' Y').hom =
      crossExpHom p X Y ≫
        (LogNilpotentModule.symmetricSwapIso X Y).hom ≫
        LogNilpotentModule.tensorHom g f
  rw [← Category.assoc, crossExp_naturality p f g, Category.assoc,
    symmetricSwap_naturality f g]

end InfoGeometry.Categorical.LogNilpotentPhysicalBraiding
