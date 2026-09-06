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
  ext x y z
  simp [scaledCrossEnd, crossTensorEnd,
    scaledLeftTripleCross, scaledRightTripleCross,
    leftTripleCross, rightTripleCross,
    LogEndModule.tensorObj_N_tmul, TensorProduct.map_tmul,
    smul_add, add_smul]

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
