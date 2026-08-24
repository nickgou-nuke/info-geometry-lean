import Mathlib.Tactic
import InfoGeometry.Physics.ChiralTensorRecoupling

/-!
# Tensor-product spin/isospin representation

The two physical degree-zero sectors act on separate tensor factors.  This is
the concrete finite representation layer; the abstract five-grading remains a
separate transition algebra.
-/

namespace InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation

open Algebra.TensorProduct
open ChiralTensorRecoupling
open InfoGeometry.Physics.ChiralCausalCone

noncomputable section

def spinAction (A : M2C) : SpinPair := A ⊗ₜ[ℂ] (1 : M2C)

def isospinAction (B : M2C) : SpinPair := (1 : M2C) ⊗ₜ[ℂ] B

theorem spin_isospin_actions_commute (A B : M2C) :
    spinAction A * isospinAction B =
      isospinAction B * spinAction A := by
  unfold spinAction isospinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  simp [mul_comm]

theorem spin_action_preserves_commutator (A B : M2C) :
    spinAction A * spinAction B - spinAction B * spinAction A =
      (A * B - B * A) ⊗ₜ[ℂ] (1 : M2C) := by
  unfold spinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  rw [← TensorProduct.sub_tmul]
  simp

theorem isospin_action_preserves_commutator (A B : M2C) :
    isospinAction A * isospinAction B - isospinAction B * isospinAction A =
      (1 : M2C) ⊗ₜ[ℂ] (A * B - B * A) := by
  unfold isospinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  rw [← TensorProduct.tmul_sub]
  simp

end

end InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
