import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-! Independent `ℤ₂` twists for the two physical tensor factors. -/

def spinTwist (x : SpinPair) : SpinPair :=
  spinChirality * x * spinChirality

def isospinTwist (x : SpinPair) : SpinPair :=
  isospinChirality * x * isospinChirality

theorem spinTwist_involutive (x : SpinPair) :
    spinTwist (spinTwist x) = x := by
  unfold spinTwist
  calc
    spinChirality * (spinChirality * x * spinChirality) * spinChirality =
        (spinChirality * spinChirality) * x *
          (spinChirality * spinChirality) := by noncomm_ring
    _ = x := by rw [spinChirality_sq]; simp

theorem isospinTwist_involutive (x : SpinPair) :
    isospinTwist (isospinTwist x) = x := by
  unfold isospinTwist
  calc
    isospinChirality * (isospinChirality * x * isospinChirality) *
        isospinChirality =
      (isospinChirality * isospinChirality) * x *
        (isospinChirality * isospinChirality) := by noncomm_ring
    _ = x := by rw [isospinChirality_sq]; simp

theorem spinTwist_isospinTwist_commute (x : SpinPair) :
    spinTwist (isospinTwist x) =
      isospinTwist (spinTwist x) := by
  unfold spinTwist isospinTwist
  have hcomm := spinChirality_isospinChirality_commute
  calc
    spinChirality * (isospinChirality * x * isospinChirality) *
        spinChirality =
      (spinChirality * isospinChirality) * x *
        (isospinChirality * spinChirality) := by noncomm_ring
    _ = (isospinChirality * spinChirality) * x *
        (spinChirality * isospinChirality) := by rw [hcomm]
    _ = isospinChirality * (spinChirality * x * spinChirality) *
        isospinChirality := by noncomm_ring

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

theorem spin_action_preserves_square (A : M2C) (hA : A * A = 1) :
    spinAction A * spinAction A = (1 : SpinPair) := by
  unfold spinAction
  rw [tmul_mul_tmul, hA]
  simp [Algebra.TensorProduct.one_def]

theorem isospin_action_preserves_square (A : M2C) (hA : A * A = 1) :
    isospinAction A * isospinAction A = (1 : SpinPair) := by
  unfold isospinAction
  rw [tmul_mul_tmul, hA]
  simp [Algebra.TensorProduct.one_def]

theorem pauli_spin_squares :
    spinAction I₁ * spinAction I₁ = (1 : SpinPair) ∧
      spinAction I₂ * spinAction I₂ = (1 : SpinPair) ∧
      spinAction I₃ * spinAction I₃ = (1 : SpinPair) := by
  exact ⟨spin_action_preserves_square I₁ I₁_sq,
    spin_action_preserves_square I₂ I₂_sq,
    spin_action_preserves_square I₃ I₃_sq⟩

theorem pauli_isospin_squares :
    isospinAction I₁ * isospinAction I₁ = (1 : SpinPair) ∧
      isospinAction I₂ * isospinAction I₂ = (1 : SpinPair) ∧
      isospinAction I₃ * isospinAction I₃ = (1 : SpinPair) := by
  exact ⟨isospin_action_preserves_square I₁ I₁_sq,
    isospin_action_preserves_square I₂ I₂_sq,
    isospin_action_preserves_square I₃ I₃_sq⟩

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
