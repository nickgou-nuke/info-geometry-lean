/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors.
-/
import InfoGeometry.Canonical.CausalVortexPauliPositivity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Spectral projectors of the finite Cooper-pair number operator

The polynomial `N^2 = 2N` gives the two algebraic spectral values `0` and `2`.
The projectors below are defined by the corresponding Lagrange polynomials;
all identities are proved directly in the finite matrix algebra.
-/

namespace CausalVortex

open Matrix
open InfoGeometry.Physics.ChiralPoincareSouriauBridge

noncomputable def pauliProjectorTwo : M2C :=
  (1 / 2 : ℂ) • pauliNumberOperator

noncomputable def pauliProjectorZero : M2C :=
  (1 : M2C) - pauliProjectorTwo

theorem pauliProjectorTwo_idempotent :
    pauliProjectorTwo * pauliProjectorTwo = pauliProjectorTwo := by
  unfold pauliProjectorTwo
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [pauli_number_operator_quadratic]
  norm_num [smul_smul]

theorem pauliProjectorZero_idempotent :
    pauliProjectorZero * pauliProjectorZero = pauliProjectorZero := by
  unfold pauliProjectorZero
  calc
    (1 - pauliProjectorTwo) * (1 - pauliProjectorTwo) =
        1 - pauliProjectorTwo - pauliProjectorTwo +
          pauliProjectorTwo * pauliProjectorTwo := by noncomm_ring
    _ = 1 - pauliProjectorTwo := by
      rw [pauliProjectorTwo_idempotent]
      abel

theorem pauliProjectors_sum :
    pauliProjectorZero + pauliProjectorTwo = (1 : M2C) := by
  unfold pauliProjectorZero
  simp

theorem pauliProjectors_orthogonal :
    pauliProjectorZero * pauliProjectorTwo = 0 ∧
      pauliProjectorTwo * pauliProjectorZero = 0 := by
  unfold pauliProjectorZero
  constructor
  · calc
      (1 - pauliProjectorTwo) * pauliProjectorTwo =
          pauliProjectorTwo - pauliProjectorTwo * pauliProjectorTwo := by
            noncomm_ring
      _ = 0 := by rw [pauliProjectorTwo_idempotent]; simp
  · calc
      pauliProjectorTwo * (1 - pauliProjectorTwo) =
          pauliProjectorTwo - pauliProjectorTwo * pauliProjectorTwo := by
            noncomm_ring
      _ = 0 := by rw [pauliProjectorTwo_idempotent]; simp

theorem pauliNumberOperator_on_projectorTwo :
    pauliNumberOperator * pauliProjectorTwo =
      (2 : ℂ) • pauliProjectorTwo := by
  unfold pauliProjectorTwo
  rw [Matrix.mul_smul, pauli_number_operator_quadratic]
  norm_num [smul_smul]

theorem pauliNumberOperator_on_projectorZero :
    pauliNumberOperator * pauliProjectorZero = 0 := by
  unfold pauliProjectorZero
  rw [mul_sub, mul_one, pauliNumberOperator_on_projectorTwo]
  simp [pauliProjectorTwo]

theorem pauliProjectorTwo_eigen_iff (v : PauliVector) :
    pauliProjectorTwo.mulVec v = v ↔
      pauliNumberOperator.mulVec v = (2 : ℂ) • v := by
  constructor
  · intro h
    have h' := congrArg (fun u => (2 : ℂ) • u) h
    simpa [pauliProjectorTwo, Matrix.smul_mulVec, smul_smul] using h'
  · intro h
    rw [pauliProjectorTwo, Matrix.smul_mulVec]
    calc
      (1 / 2 : ℂ) • pauliNumberOperator.mulVec v =
          (1 / 2 : ℂ) • ((2 : ℂ) • v) := by rw [h]
      _ = v := by simp [smul_smul]

theorem pauliProjectorZero_eigen_iff (v : PauliVector) :
    pauliProjectorZero.mulVec v = v ↔
      pauliNumberOperator.mulVec v = 0 := by
  constructor
  · intro h
    have hform : pauliProjectorZero.mulVec v =
        v - pauliProjectorTwo.mulVec v := by
      unfold pauliProjectorZero
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hform] at h
    have hp : pauliProjectorTwo.mulVec v = 0 := by
      have hz := congrArg (fun u => v - u) h
      calc
        pauliProjectorTwo.mulVec v =
            v - (v - pauliProjectorTwo.mulVec v) := by abel
        _ = v - v := hz
        _ = 0 := sub_self v
    have hhalf : (1 / 2 : ℂ) • pauliNumberOperator.mulVec v = 0 := by
      simpa [pauliProjectorTwo, Matrix.smul_mulVec] using hp
    have h'' := congrArg (fun u => (2 : ℂ) • u) hhalf
    simpa [smul_smul] using h''
  · intro h
    have hp : pauliProjectorTwo.mulVec v = 0 := by
      simp [pauliProjectorTwo, Matrix.smul_mulVec, h]
    have hform : pauliProjectorZero.mulVec v =
        v - pauliProjectorTwo.mulVec v := by
      unfold pauliProjectorZero
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hform, hp]
    simp

end CausalVortex
