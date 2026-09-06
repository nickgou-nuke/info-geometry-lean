import InfoGeometry.Krein.KreinSpace
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The operator-level left/right action on a Krein carrier

This file packages the existing bounded-operator action on `End(H)` with the
opposite multiplication on the right.  It proves the pure-tensor composition
law used by a bimodule action.  It does **not** identify a represented right
action with an analytic von Neumann commutant or assert a standard-form
theorem.
-/

noncomputable section

namespace InfoGeometry.Krein

open KreinSpace
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H]

local notation "EndH" => H →L[ℝ] H

/-- Left multiplication on the operator carrier. -/
def leftOperatorAction (A : EndH) : EndH →ₗ[ℝ] EndH :=
  { toFun := fun X => A.comp X
    map_add' := by
      intro X Y
      ext u
      simp
    map_smul' := by
      intro c X
      ext u
      simp }

/-- Right multiplication, indexed by the opposite operator algebra. -/
def rightOperatorAction (B : EndHᵐᵒᵖ) : EndH →ₗ[ℝ] EndH :=
  { toFun := fun X => X.comp B.unop
    map_add' := by
      intro X Y
      ext u
      simp
    map_smul' := by
      intro c X
      ext u
      simp }

/-- The pure left/right bimodule action on `End(H)`. -/
def operatorBimoduleAction (A : EndH) (B : EndHᵐᵒᵖ) : EndH →ₗ[ℝ] EndH :=
  (leftOperatorAction A).comp (rightOperatorAction B)

@[simp] theorem operatorBimoduleAction_apply
    (A : EndH) (B : EndHᵐᵒᵖ) (X : EndH) :
    operatorBimoduleAction A B X = A.comp (X.comp B.unop) :=
  rfl

/-! The two sides commute as actions on the operator carrier. -/

theorem leftOperatorAction_rightOperatorAction_commute
    (A : EndH) (B : EndHᵐᵒᵖ) (X : EndH) :
    leftOperatorAction A (rightOperatorAction B X) =
      rightOperatorAction B (leftOperatorAction A X) := by
  ext u
  simp [leftOperatorAction, rightOperatorAction, ContinuousLinearMap.comp_assoc]

@[simp] theorem leftOperatorAction_add
    (A C X : EndH) :
    leftOperatorAction (A + C) X =
      leftOperatorAction A X + leftOperatorAction C X := by
  ext u
  simp [leftOperatorAction]

@[simp] theorem leftOperatorAction_smul
    (c : ℝ) (A X : EndH) :
    leftOperatorAction (c • A) X = c • leftOperatorAction A X := by
  ext u
  simp [leftOperatorAction]

@[simp] theorem leftOperatorAction_one (X : EndH) :
    leftOperatorAction (1 : EndH) X = X := by
  ext u
  simp [leftOperatorAction]

/-! Opposite multiplication is the order reversal required by the right action. -/

theorem operatorBimoduleAction_pure_mul
    (A C : EndH) (B D : EndHᵐᵒᵖ) (X : EndH) :
    operatorBimoduleAction (A.comp C) (B * D) X =
      operatorBimoduleAction A B (operatorBimoduleAction C D X) := by
  ext u
  simp [operatorBimoduleAction, leftOperatorAction, rightOperatorAction,
    ContinuousLinearMap.comp_assoc]

/-! The opposite multiplication gives the right-module composition order. -/

theorem rightOperatorAction_mul
    (B D : EndHᵐᵒᵖ) (X : EndH) :
    rightOperatorAction (B * D) X =
      rightOperatorAction B (rightOperatorAction D X) := by
  ext u
  simp [rightOperatorAction, ContinuousLinearMap.comp_assoc]

@[simp] theorem rightOperatorAction_add
    (B D : EndHᵐᵒᵖ) (X : EndH) :
    rightOperatorAction (B + D) X =
      rightOperatorAction B X + rightOperatorAction D X := by
  ext u
  simp [rightOperatorAction]

@[simp] theorem rightOperatorAction_zero (X : EndH) :
    rightOperatorAction (0 : EndHᵐᵒᵖ) X = 0 := by
  ext u
  simp [rightOperatorAction]

@[simp] theorem rightOperatorAction_smul (c : ℝ) (B : EndHᵐᵒᵖ) (X : EndH) :
    rightOperatorAction (c • B) X = c • rightOperatorAction B X := by
  ext u
  simp [rightOperatorAction]

@[simp] theorem rightOperatorAction_one (X : EndH) :
    rightOperatorAction (1 : EndHᵐᵒᵖ) X = X := by
  ext u
  simp [rightOperatorAction]

/-! The already verified action supplies the concrete opposite-algebra module. -/

noncomputable instance rightOperatorModule : Module EndHᵐᵒᵖ EndH where
  smul B X := rightOperatorAction B X
  one_smul X := rightOperatorAction_one X
  mul_smul B D X := (rightOperatorAction_mul B D X).symm
  smul_add B X Y := by
    ext u
    simp [rightOperatorAction]
  smul_zero B := by
    ext u
    simp [rightOperatorAction]
  add_smul B D X := by exact rightOperatorAction_add B D X
  zero_smul X := rightOperatorAction_zero X

@[simp] theorem operatorBimoduleAction_one
    (X : EndH) :
    operatorBimoduleAction (1 : EndH) (1 : EndHᵐᵒᵖ) X = X := by
  ext u
  simp [operatorBimoduleAction, leftOperatorAction, rightOperatorAction]

/-! The Hilbert-positive conjugation already present in `KreinSpace` is one
pure bimodule action with the adjoint in the opposite slot. -/

theorem operatorBimoduleAction_adjoint_eq_positiveConjugation
    (A X : EndH) :
    operatorBimoduleAction A (MulOpposite.op (ContinuousLinearMap.adjoint A)) X =
      positiveConjugation A X :=
  rfl

/-- The left/right opposite-algebra action preserves Hilbert positivity. -/
theorem operatorBimoduleAction_adjoint_inner_nonneg
    (A X : EndH)
    (hX : ∀ u : H, 0 ≤ ⟪X u, u⟫_ℝ)
    (u : H) :
    0 ≤
      ⟪operatorBimoduleAction A
          (MulOpposite.op (ContinuousLinearMap.adjoint A)) X u, u⟫_ℝ := by
  rw [operatorBimoduleAction_adjoint_eq_positiveConjugation]
  exact KreinSpace.inner_positiveConjugation_nonneg A X hX u

/-! ## Tensor-product lift of the bimodule action -/

/-! ### The canonical operator-valued pre-inner product -/

/- The `End(H)`-valued pre-inner product on the operator carrier. -/
noncomputable def operatorModuleInner (X Y : EndH) : EndH := star X * Y

@[simp] theorem operatorModuleInner_add_left (X Y Z : EndH) :
    operatorModuleInner (X + Y) Z =
      operatorModuleInner X Z + operatorModuleInner Y Z := by
  ext u
  simp [operatorModuleInner, add_mul]

@[simp] theorem operatorModuleInner_add_right (X Y Z : EndH) :
    operatorModuleInner X (Y + Z) =
      operatorModuleInner X Y + operatorModuleInner X Z := by
  ext u
  simp [operatorModuleInner, mul_add]

@[simp] theorem operatorModuleInner_smul_left (c : ℝ) (X Y : EndH) :
    operatorModuleInner (c • X) Y = c • operatorModuleInner X Y := by
  ext u
  simp [operatorModuleInner]

@[simp] theorem operatorModuleInner_smul_right (c : ℝ) (X Y : EndH) :
    operatorModuleInner X (c • Y) = c • operatorModuleInner X Y := by
  ext u
  simp [operatorModuleInner]

theorem operatorModuleInner_conj_symm (X Y : EndH) :
    star (operatorModuleInner X Y) = operatorModuleInner Y X := by
  ext u
  simp [operatorModuleInner]

theorem operatorModuleInner_right_action (X Y B : EndH) :
    operatorModuleInner X (Y * B) = operatorModuleInner X Y * B := by
  ext u
  simp [operatorModuleInner, mul_assoc]

/-! The left action is adjointable for the operator-valued pre-inner product. -/

theorem operatorModuleInner_left_action (A X Y : EndH) :
    operatorModuleInner (A * X) Y = star X * star A * Y := by
  dsimp [operatorModuleInner]
  rw [star_mul, mul_assoc]

/-! The pre-inner product is compatible with the opposite right action. -/

theorem operatorModuleInner_right_op_action
    (X Y : EndH) (B : EndHᵐᵒᵖ) :
    operatorModuleInner X (rightOperatorAction B Y) =
      rightOperatorAction B (operatorModuleInner X Y) := by
  ext u
  simp [operatorModuleInner, rightOperatorAction, ContinuousLinearMap.comp_assoc]

/-! The two-sided transport law used by the tensor-action. -/

theorem operatorModuleInner_two_sided_action
    (A X Y : EndH) (B : EndHᵐᵒᵖ) :
    operatorModuleInner (A * X) (rightOperatorAction B Y) =
      star X * star A * rightOperatorAction B Y := by
  dsimp [operatorModuleInner]
  rw [star_mul, mul_assoc]

/-- The left action as a linear map in its operator label. -/
def leftOperatorRepresentation : EndH →ₗ[ℝ] Module.End ℝ EndH :=
  { toFun := leftOperatorAction
    map_add' := by
      intro A B
      ext X u
      simp [leftOperatorAction]
    map_smul' := by
      intro c A
      ext X u
      simp [leftOperatorAction] }

/-- The right opposite action as a linear map in its operator label. -/
def rightOperatorRepresentation : EndHᵐᵒᵖ →ₗ[ℝ] Module.End ℝ EndH :=
  { toFun := rightOperatorAction
    map_add' := by
      intro A B
      ext X u
      simp [rightOperatorAction]
    map_smul' := by
      intro c A
      ext X u
      simp [rightOperatorAction] }

noncomputable def leftOperatorAlgHom : EndH →ₐ[ℝ] Module.End ℝ EndH :=
  AlgHom.ofLinearMap leftOperatorRepresentation (by
    ext X u
    simp [leftOperatorRepresentation, leftOperatorAction]) (by
    intro A B
    ext X u
    simp [leftOperatorRepresentation, leftOperatorAction,
      Module.End.mul_apply, ContinuousLinearMap.comp_assoc])

noncomputable def rightOperatorAlgHom : EndHᵐᵒᵖ →ₐ[ℝ] Module.End ℝ EndH :=
  AlgHom.ofLinearMap rightOperatorRepresentation (by
    ext X u
    simp [rightOperatorRepresentation, rightOperatorAction]) (by
    intro A B
    ext X u
    simp [rightOperatorRepresentation, rightOperatorAction,
      Module.End.mul_apply, ContinuousLinearMap.comp_assoc])

theorem leftOperatorRepresentation_commutes_right
    (A : EndH) (B : EndHᵐᵒᵖ) :
    Commute (leftOperatorAlgHom A) (rightOperatorAlgHom B) := by
  rw [Commute]
  ext X u
  simp [leftOperatorAlgHom, rightOperatorAlgHom, leftOperatorRepresentation,
    rightOperatorRepresentation, leftOperatorAction, rightOperatorAction,
    Module.End.mul_apply, ContinuousLinearMap.comp_assoc]

/-- The genuine algebraic bimodule representation of the tensor product.

This is an algebraic operator representation.  No claim is made here that the
right factor is an analytic von Neumann commutant. -/
noncomputable def operatorBimoduleTensorAction :
    TensorProduct ℝ EndH EndHᵐᵒᵖ →ₐ[ℝ] Module.End ℝ EndH :=
  _root_.Algebra.TensorProduct.lift leftOperatorAlgHom rightOperatorAlgHom
    leftOperatorRepresentation_commutes_right

@[simp] theorem operatorBimoduleTensorAction_tmul
    (A : EndH) (B : EndHᵐᵒᵖ) (X : EndH) :
    operatorBimoduleTensorAction (A ⊗ₜ[ℝ] B) X =
      operatorBimoduleAction A B X := by
  rfl

/-- Positivity of the adjoint-paired pure tensor action. -/
theorem operatorBimoduleTensorAction_tmul_adjoint_inner_nonneg
    (A X : EndH)
    (hX : ∀ u : H, 0 ≤ ⟪X u, u⟫_ℝ)
    (u : H) :
    0 ≤
      ⟪operatorBimoduleTensorAction
          (A ⊗ₜ[ℝ] MulOpposite.op (ContinuousLinearMap.adjoint A)) X u, u⟫_ℝ := by
  rw [operatorBimoduleTensorAction_tmul]
  exact operatorBimoduleAction_adjoint_inner_nonneg A X hX u

end InfoGeometry.Krein
