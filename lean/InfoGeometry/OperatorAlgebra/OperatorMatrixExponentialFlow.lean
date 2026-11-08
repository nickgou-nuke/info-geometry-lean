/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Exponential flow for operator-valued two-by-two matrices

This owner defines the complex-time exponential directly in `M₂(B)`, for a
complete normed complex operator algebra `B`. Unlike a scalar matrix flow
mapped into `B`, the generator here has arbitrary, potentially noncommuting
operator entries. It proves the one-parameter group laws. The projective
Riccati chart remains a separate algebraic owner, since
its normalized chart requires additional curve and denominator data.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorMatrixExponentialFlow

open InfoGeometry.OperatorAlgebra
open scoped Matrix.Norms.Operator

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
  [NormedAlgebra ℚ B] [CompleteSpace B]

/-- Complex-time exponential of an arbitrary operator-valued `2 × 2`
generator. -/
def flow (G : OperatorMatrix B) (t : ℂ) : OperatorMatrix B :=
  NormedSpace.exp (t • G)

/-- The direct operator exponential obeys the additive-time law. -/
theorem flow_add (G : OperatorMatrix B) (s t : ℂ) :
    flow G (s + t) = flow G s * flow G t := by
  rw [flow, flow, flow, add_smul]
  exact Matrix.exp_add_of_commute (s • G) (t • G)
    (((Commute.refl G).smul_left s).smul_right t)

@[simp] theorem flow_zero (G : OperatorMatrix B) :
    flow G 0 = 1 := by
  simp [flow]

/-- Negative time is a two-sided inverse for the operator-matrix flow. -/
theorem flow_inverse (G : OperatorMatrix B) (t : ℂ) :
    flow G (-t) * flow G t = 1 ∧ flow G t * flow G (-t) = 1 := by
  constructor
  · rw [← flow_add G (-t) t, neg_add_cancel, flow_zero]
  · rw [← flow_add G t (-t), add_neg_cancel, flow_zero]

/-- Action of the direct operator-matrix exponential on an arbitrary pair
of operators. -/
def action (G : OperatorMatrix B) (t : ℂ) (v : OperatorPair B) : OperatorPair B :=
  operatorMobiusAction (flow G t) v

/-- The exponential action composes in additive time, preserving the matrix
order in the operator-valued Möbius action. -/
theorem action_add (G : OperatorMatrix B) (s t : ℂ) (v : OperatorPair B) :
    action G (s + t) v = action G s (action G t v) := by
  unfold action
  rw [flow_add, operatorMobiusAction_mul]

/-- Negative time reverses the direct operator-matrix action. -/
theorem action_inverse (G : OperatorMatrix B) (t : ℂ) (v : OperatorPair B) :
    action G (-t) (action G t v) = v ∧
      action G t (action G (-t) v) = v := by
  constructor
  · rw [← action_add G (-t) t v, neg_add_cancel, action, flow_zero,
      operatorMobiusAction_one]
  · rw [← action_add G t (-t) v, add_neg_cancel, action, flow_zero,
      operatorMobiusAction_one]

end InfoGeometry.OperatorAlgebra.OperatorMatrixExponentialFlow

end
