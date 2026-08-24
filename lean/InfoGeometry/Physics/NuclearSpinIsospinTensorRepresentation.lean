import Mathlib.Tactic
import InfoGeometry.Physics.ChiralTensorRecoupling
import InfoGeometry.External.Auto.WeakIsospinSU2

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
open WeakIsospinSU2

noncomputable section

def spinAction (A : M2C) : SpinPair := A ⊗ₜ[ℂ] (1 : M2C)

def isospinAction (B : M2C) : SpinPair := (1 : M2C) ⊗ₜ[ℂ] B

/-! The two physical Cartan/chirality readouts.  They are kept distinct from
the generic circular involution API: no circular axis is selected here. -/

def spinChirality : SpinPair := spinAction σ3c

def isospinChirality : SpinPair := isospinAction σ3c

theorem spinChirality_sq :
    spinChirality * spinChirality = (1 : SpinPair) := by
  unfold spinChirality spinAction
  rw [tmul_mul_tmul, σ3c_sq]
  simp [Algebra.TensorProduct.one_def]

theorem isospinChirality_sq :
    isospinChirality * isospinChirality = (1 : SpinPair) := by
  unfold isospinChirality isospinAction
  rw [tmul_mul_tmul, σ3c_sq]
  simp [Algebra.TensorProduct.one_def]

theorem spinChirality_isospinChirality_commute :
    spinChirality * isospinChirality =
      isospinChirality * spinChirality := by
  unfold spinChirality isospinChirality spinAction isospinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  simp

theorem spin_isospin_actions_commute (A B : M2C) :
    spinAction A * isospinAction B =
      isospinAction B * spinAction A := by
  unfold spinAction isospinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  simp

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

theorem pauli_spin_comm_I₁_I₂ :
    spinAction I₁ * spinAction I₂ - spinAction I₂ * spinAction I₁ =
      (2 * Complex.I) • spinAction I₃ := by
  rw [spin_action_preserves_commutator, I₁_comm_I₂]
  simp [spinAction, TensorProduct.smul_tmul]

theorem pauli_isospin_comm_I₁_I₂ :
    isospinAction I₁ * isospinAction I₂ -
        isospinAction I₂ * isospinAction I₁ =
      (2 * Complex.I) • isospinAction I₃ := by
  rw [isospin_action_preserves_commutator, I₁_comm_I₂]
  simp [isospinAction]

theorem pauli_spin_comm_I₂_I₃ :
    spinAction I₂ * spinAction I₃ - spinAction I₃ * spinAction I₂ =
      (2 * Complex.I) • spinAction I₁ := by
  rw [spin_action_preserves_commutator, I₂_comm_I₃]
  simp [spinAction, TensorProduct.smul_tmul]

theorem pauli_spin_comm_I₃_I₁ :
    spinAction I₃ * spinAction I₁ - spinAction I₁ * spinAction I₃ =
      (2 * Complex.I) • spinAction I₂ := by
  rw [spin_action_preserves_commutator, I₃_comm_I₁]
  simp [spinAction, TensorProduct.smul_tmul]

theorem pauli_isospin_comm_I₂_I₃ :
    isospinAction I₂ * isospinAction I₃ -
        isospinAction I₃ * isospinAction I₂ =
      (2 * Complex.I) • isospinAction I₁ := by
  rw [isospin_action_preserves_commutator, I₂_comm_I₃]
  simp [isospinAction]

theorem pauli_isospin_comm_I₃_I₁ :
    isospinAction I₃ * isospinAction I₁ -
        isospinAction I₁ * isospinAction I₃ =
      (2 * Complex.I) • isospinAction I₂ := by
  rw [isospin_action_preserves_commutator, I₃_comm_I₁]
  simp [isospinAction]

end

end InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
