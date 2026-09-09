import Mathlib.Tactic
import InfoGeometry.Categorical.LogNilpotentHadjiivanovExponential

/-!
# Three-leg algebra for the natural Hadjiivanov braiding

This file isolates the algebraic content of the two braided hexagons.  On a
triple tensor product the mixed logarithmic direction splits into two commuting
cross terms.  Because all terms are nilpotent, Mathlib's finite algebraic
exponential converts this additive splitting into an exact multiplicative
splitting.

The definitions use Mathlib's native tensor algebra homomorphisms and
`LinearEquiv.conjAlgEquiv`; no hand-written exponential or matrix carrier is
introduced.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentHadjiivanovHexagonAlgebra

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentMonoidalCategory
open InfoGeometry.Categorical.LogNilpotentHadjiivanovExponential

/-- The `(X,Y)` mixed logarithmic term, transported to the right-associated
carrier `X ⊗ (Y ⊗ Z)`. -/
def rightCross12 (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗ (Y ⊗ Z)) :=
  ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ)
    ((Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z) (crossEnd X Y))

/-- The `(X,Z)` mixed logarithmic term on `X ⊗ (Y ⊗ Z)`, obtained by moving
`X,Z` next to one another with Mathlib's `leftComm`. -/
def rightCross13 (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ (X ⊗ (Y ⊗ Z)) :=
  (((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
    ((Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y) (crossEnd X Z))

@[simp]
theorem rightCross12_tmul
    (X Y Z : LogNilpotentModule ℂ) (x : X) (y : Y) (z : Z) :
    rightCross12 X Y Z (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) =
      X.N x ⊗ₜ[ℂ] (Y.N y ⊗ₜ[ℂ] z) := by
  simp [rightCross12, LinearEquiv.conjAlgEquiv_apply,
    Module.End.rTensorAlgHom, LinearMap.comp_apply,
    crossEnd, InfoGeometry.Categorical.LogEndModuleNilpotentClosure.crossTensorEnd]

@[simp]
theorem rightCross13_tmul
    (X Y Z : LogNilpotentModule ℂ) (x : X) (y : Y) (z : Z) :
    rightCross13 X Y Z (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) =
      X.N x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] Z.N z) := by
  simp [rightCross13, LinearEquiv.conjAlgEquiv_apply,
    Module.End.lTensorAlgHom, LinearMap.comp_apply,
    crossEnd, InfoGeometry.Categorical.LogEndModuleNilpotentClosure.crossTensorEnd]

/-- Primitive coproduct splitting in the second tensor argument. -/
theorem crossEnd_right_decompose
    (X Y Z : LogNilpotentModule ℂ) :
    crossEnd X (Y ⊗ Z) = rightCross12 X Y Z + rightCross13 X Y Z := by
  ext x y z
  simp [crossEnd, InfoGeometry.Categorical.LogEndModuleNilpotentClosure.crossTensorEnd,
    LogEndModule.tensorObj_N_tmul]

/-- The two right-associated cross legs commute. -/
theorem rightCross_commute (X Y Z : LogNilpotentModule ℂ) :
    Commute (rightCross12 X Y Z) (rightCross13 X Y Z) := by
  apply Commute.eq
  ext x y z
  simp [Module.End.mul_eq_comp, LinearMap.comp_apply]

/-- Nilpotence of the `(X,Y)` cross leg follows functorially from nilpotence of
`crossEnd X Y`. -/
theorem rightCross12_isNilpotent (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (rightCross12 X Y Z) := by
  exact ((crossEnd_isNilpotent X Y).map
      (Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z)).map
    ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ)

/-- Nilpotence of the `(X,Z)` cross leg. -/
theorem rightCross13_isNilpotent (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (rightCross13 X Y Z) := by
  exact ((crossEnd_isNilpotent X Z).map
      (Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y)).map
    (((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm)

/-- Exact exponential splitting in the second argument.  The factor order is
chosen to match categorical left-to-right composition: first the `(X,Y)`
correction, then the `(X,Z)` correction. -/
theorem crossExpEnd_right_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpEnd p X (Y ⊗ Z) =
      IsNilpotent.exp (p • rightCross13 X Y Z) *
        IsNilpotent.exp (p • rightCross12 X Y Z) := by
  rw [crossExpEnd, crossEnd_right_decompose, smul_add, add_comm]
  apply IsNilpotent.exp_add_of_commute
  · exact (rightCross_commute X Y Z).symm.smul_left p |>.smul_right p
  · exact (rightCross13_isNilpotent X Y Z).smul p
  · exact (rightCross12_isNilpotent X Y Z).smul p

/-- Exponentiating the `(X,Y)` leg is the associator transport of the pair
exponential tensored with the spectator `Z`. -/
theorem exp_rightCross12
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (p • rightCross12 X Y Z) =
      ((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ)
        ((Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z) (crossExpEnd p X Y)) := by
  let A : Module.End ℂ (X ⊗ Y) := p • crossEnd X Y
  let f := Module.End.rTensorAlgHom ℂ (X ⊗ Y) Z
  let e := (TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ
  have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p X Y
  have hf := hA.map_exp f
  have hef := (hA.map f).map_exp e
  symm
  calc
    e (f (crossExpEnd p X Y)) = e (f (IsNilpotent.exp A)) := by rfl
    _ = e (IsNilpotent.exp (f A)) := by rw [hf]
    _ = IsNilpotent.exp (e (f A)) := hef
    _ = IsNilpotent.exp (p • rightCross12 X Y Z) := by
      congr 2
      simp [A, f, e, rightCross12]

/-- Exponentiating the `(X,Z)` leg is the `leftComm` pullback of the pair
exponential with spectator `Y`. -/
theorem exp_rightCross13
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent.exp (p • rightCross13 X Y Z) =
      (((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
        ((Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y) (crossExpEnd p X Z)) := by
  let A : Module.End ℂ (X ⊗ Z) := p • crossEnd X Z
  let f := Module.End.lTensorAlgHom ℂ (X ⊗ Z) Y
  let e := ((TensorProduct.leftComm ℂ X Y Z).conjAlgEquiv ℂ).symm
  have hA : IsNilpotent A := scaledCrossEnd_isNilpotent p X Z
  have hf := hA.map_exp f
  have hef := (hA.map f).map_exp e
  symm
  calc
    e (f (crossExpEnd p X Z)) = e (f (IsNilpotent.exp A)) := by rfl
    _ = e (IsNilpotent.exp (f A)) := by rw [hf]
    _ = IsNilpotent.exp (e (f A)) := hef
    _ = IsNilpotent.exp (p • rightCross13 X Y Z) := by
      congr 2
      simp [A, f, e, rightCross13]

/-! ## Left-associated splitting -/

/-- The `(X,Z)` cross term on `(X ⊗ Y) ⊗ Z`, transported through
Mathlib's `rightComm`. -/
def leftCross13 (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ ((X ⊗ Y) ⊗ Z) :=
  (((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm)
    ((Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y) (crossEnd X Z))

/-- The `(Y,Z)` cross term on `(X ⊗ Y) ⊗ Z`, obtained from the
right-associated carrier by the inverse associator transport. -/
def leftCross23 (X Y Z : LogNilpotentModule ℂ) :
    Module.End ℂ ((X ⊗ Y) ⊗ Z) :=
  (((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm)
    ((Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X) (crossEnd Y Z))

@[simp]
theorem leftCross13_tmul
    (X Y Z : LogNilpotentModule ℂ) (x : X) (y : Y) (z : Z) :
    leftCross13 X Y Z ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      (X.N x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] Z.N z := by
  simp [leftCross13, LinearEquiv.conjAlgEquiv_apply,
    Module.End.rTensorAlgHom, LinearMap.comp_apply,
    crossEnd, InfoGeometry.Categorical.LogEndModuleNilpotentClosure.crossTensorEnd]

@[simp]
theorem leftCross23_tmul
    (X Y Z : LogNilpotentModule ℂ) (x : X) (y : Y) (z : Z) :
    leftCross23 X Y Z ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      (x ⊗ₜ[ℂ] Y.N y) ⊗ₜ[ℂ] Z.N z := by
  simp [leftCross23, LinearEquiv.conjAlgEquiv_apply,
    Module.End.lTensorAlgHom, LinearMap.comp_apply,
    crossEnd, InfoGeometry.Categorical.LogEndModuleNilpotentClosure.crossTensorEnd]

/-- Primitive coproduct splitting in the first tensor argument. -/
theorem crossEnd_left_decompose
    (X Y Z : LogNilpotentModule ℂ) :
    crossEnd (X ⊗ Y) Z = leftCross13 X Y Z + leftCross23 X Y Z := by
  ext x y z
  simp [crossEnd, InfoGeometry.Categorical.LogEndModuleNilpotentClosure.crossTensorEnd,
    LogEndModule.tensorObj_N_tmul]

/-- The two left-associated cross legs commute. -/
theorem leftCross_commute (X Y Z : LogNilpotentModule ℂ) :
    Commute (leftCross13 X Y Z) (leftCross23 X Y Z) := by
  apply Commute.eq
  ext x y z
  simp [Module.End.mul_eq_comp, LinearMap.comp_apply]

/-- Nilpotence of the transported `(X,Z)` leg. -/
theorem leftCross13_isNilpotent (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (leftCross13 X Y Z) := by
  exact ((crossEnd_isNilpotent X Z).map
      (Module.End.rTensorAlgHom ℂ (X ⊗ Z) Y)).map
    (((TensorProduct.rightComm ℂ X Y Z).conjAlgEquiv ℂ).symm)

/-- Nilpotence of the transported `(Y,Z)` leg. -/
theorem leftCross23_isNilpotent (X Y Z : LogNilpotentModule ℂ) :
    IsNilpotent (leftCross23 X Y Z) := by
  exact ((crossEnd_isNilpotent Y Z).map
      (Module.End.lTensorAlgHom ℂ (Y ⊗ Z) X)).map
    (((TensorProduct.assoc ℂ X Y Z).conjAlgEquiv ℂ).symm)

/-- Exact exponential splitting in the first argument, ordered for categorical
left-to-right composition. -/
theorem crossExpEnd_left_split
    (p : ℂ) (X Y Z : LogNilpotentModule ℂ) :
    crossExpEnd p (X ⊗ Y) Z =
      IsNilpotent.exp (p • leftCross23 X Y Z) *
        IsNilpotent.exp (p • leftCross13 X Y Z) := by
  rw [crossExpEnd, crossEnd_left_decompose, smul_add, add_comm]
  apply IsNilpotent.exp_add_of_commute
  · exact (leftCross_commute X Y Z).symm.smul_left p |>.smul_right p
  · exact (leftCross23_isNilpotent X Y Z).smul p
  · exact (leftCross13_isNilpotent X Y Z).smul p

end InfoGeometry.Categorical.LogNilpotentHadjiivanovHexagonAlgebra
