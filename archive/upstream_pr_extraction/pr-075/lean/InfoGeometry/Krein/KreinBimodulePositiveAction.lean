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

/-! Opposite multiplication is the order reversal required by the right action. -/

theorem operatorBimoduleAction_pure_mul
    (A C : EndH) (B D : EndHᵐᵒᵖ) (X : EndH) :
    operatorBimoduleAction (A.comp C) (B * D) X =
      operatorBimoduleAction A B (operatorBimoduleAction C D X) := by
  ext u
  simp [operatorBimoduleAction, leftOperatorAction, rightOperatorAction,
    ContinuousLinearMap.comp_assoc]

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
