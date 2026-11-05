/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
import InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Ordered operator covariance transport

The affine update is `C ↦ T * C * star T + Q`. Algebraic results hold in an
arbitrary associative star ring. Positivity results use full finite matrices
over an `RCLike` field, with no commutation or diagonalization hypothesis.

The innovation identities retain the mixed Gram operator `X * Eᴴ`. Its
vanishing is an explicit sufficient hypothesis for closure. Arbitrary Gram
factors are not asserted to be centered random variables or independent noise.
Only the homogeneous part of the affine update is a linear Kraus map.
-/

namespace InfoGeometry.OperatorAlgebra.CovarianceTransport

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel

section StarRing

variable {A : Type*} [Ring A] [StarRing A]

/-- Affine covariance evolution, preserving the order of all operator factors. -/
def covarianceStep (T Q C : A) : A := T * C * star T + Q

/-- The noise cancels when comparing two initial covariance operators. -/
theorem covarianceStep_sub (T Q C D : A) :
    covarianceStep T Q C - covarianceStep T Q D = T * (C - D) * star T := by
  unfold covarianceStep
  noncomm_ring

/-- Later transport multiplies earlier transport on the left. -/
theorem covarianceStep_comp (T₂ Q₂ T₁ Q₁ C : A) :
    covarianceStep T₂ Q₂ (covarianceStep T₁ Q₁ C) =
      covarianceStep (T₂ * T₁) (covarianceStep T₂ Q₂ Q₁) C := by
  simp only [covarianceStep, star_mul]
  noncomm_ring

theorem covarianceStep_adjoint (T Q C : A) :
    star (covarianceStep T Q C) = covarianceStep T (star Q) (star C) := by
  simp only [covarianceStep, star_add, star_mul, star_star]
  noncomm_ring

theorem covarianceStep_selfAdjoint (T : A) {Q C : A}
    (hC : star C = C) (hQ : star Q = Q) :
    star (covarianceStep T Q C) = covarianceStep T Q C := by
  rw [covarianceStep_adjoint, hC, hQ]

/-- The existing finite Kraus owner supplies the homogeneous transport. -/
theorem covarianceStep_zero_eq_krausChannel (T C : A) :
    covarianceStep T 0 C = krausChannel (fun _ : Unit => T) C := by
  simp [covarianceStep, krausChannel]

/-- Conjugation by an isometry intertwines the whole affine update. -/
theorem covarianceStep_unitaryConjugation {U : A} (hU : star U * U = 1)
    (T Q C : A) :
    covarianceStep (unitaryConjugation U T) (unitaryConjugation U Q)
        (unitaryConjugation U C) =
      unitaryConjugation U (covarianceStep T Q C) := by
  simp only [covarianceStep, unitaryConjugation, star_mul, star_star]
  calc
    _ = U * T * (star U * U) * C * (star U * U) * star T * star U +
        U * Q * star U := by noncomm_ring
    _ = _ := by rw [hU]; noncomm_ring

/-- The exact residual caused by exchanging gain and mixing operators.
Nonzero commutator alone does not imply a nonzero covariance residual. -/
theorem gain_mixing_order_defect (G J Q C : A) :
    covarianceStep (G * J) Q C - covarianceStep (J * G) Q C =
      operatorCommutator G J * C * star (G * J) +
        (J * G) * C * star (operatorCommutator G J) := by
  simp only [covarianceStep, operatorCommutator, star_sub, star_mul]
  noncomm_ring

end StarRing

section Matrices

open Matrix
open scoped ComplexOrder

variable {𝕜 n m : Type*} [RCLike 𝕜]
variable [Fintype n] [DecidableEq n] [Fintype m]

/-- Exact Gram covariance of a transported amplitude and a new innovation. -/
theorem innovation_covariance (T : Matrix n n 𝕜) (X E : Matrix n m 𝕜) :
    (T * X + E) * (T * X + E)ᴴ =
      covarianceStep T (E * Eᴴ) (X * Xᴴ) +
        T * (X * Eᴴ) + (X * Eᴴ)ᴴ * Tᴴ := by
  simp only [covarianceStep, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]
  abel

omit [DecidableEq n] in
/-- The directed lag keeps the adjoint orientation of the cross moment. -/
theorem innovation_lag (T : Matrix n n 𝕜) (X E : Matrix n m 𝕜) :
    (T * X + E) * Xᴴ = T * (X * Xᴴ) + (X * Eᴴ)ᴴ := by
  simp only [Matrix.add_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem innovation_covariance_of_orthogonal (T : Matrix n n 𝕜)
    {X E : Matrix n m 𝕜} (hXE : X * Eᴴ = 0) :
    (T * X + E) * (T * X + E)ᴴ = covarianceStep T (E * Eᴴ) (X * Xᴴ) := by
  rw [innovation_covariance, hXE]
  simp

omit [DecidableEq n] in
theorem innovation_lag_of_orthogonal (T : Matrix n n 𝕜)
    {X E : Matrix n m 𝕜} (hXE : X * Eᴴ = 0) :
    (T * X + E) * Xᴴ = T * (X * Xᴴ) := by
  rw [innovation_lag, hXE]
  simp

/-- Positivity is the native positive-semidefinite matrix predicate. -/
theorem covarianceStep_posSemidef (T : Matrix n n 𝕜) {Q C : Matrix n n 𝕜}
    (hC : C.PosSemidef) (hQ : Q.PosSemidef) :
    (covarianceStep T Q C).PosSemidef :=
  (hC.mul_mul_conjTranspose_same T).add hQ

/-- Monotonicity in the Loewner order, expressed without an order-instance choice. -/
theorem covarianceStep_mono (T Q : Matrix n n 𝕜) {C D : Matrix n n 𝕜}
    (hCD : (D - C).PosSemidef) :
    (covarianceStep T Q D - covarianceStep T Q C).PosSemidef := by
  rw [covarianceStep_sub]
  exact hCD.mul_mul_conjTranspose_same T

/-- The previous and next covariances and their directed lag form one PSD block. -/
theorem joint_covariance_posSemidef (T : Matrix n n 𝕜) {Q C : Matrix n n 𝕜}
    (hC : C.PosSemidef) (hQ : Q.PosSemidef) :
    (Matrix.fromBlocks C (C * Tᴴ) (T * C) (covarianceStep T Q C)).PosSemidef := by
  have h₁ := hC.mul_mul_conjTranspose_same (Matrix.fromRows (1 : Matrix n n 𝕜) T)
  have h₂ := hQ.mul_mul_conjTranspose_same
    (Matrix.fromRows (0 : Matrix n n 𝕜) (1 : Matrix n n 𝕜))
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols] at h₁ h₂
  have h := h₁.add h₂
  simpa only [covarianceStep, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.one_mul,
    Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, Matrix.fromBlocks_add,
    add_zero, zero_add] using h

/-- Identification with the existing weighted coarse-graining covariance. -/
theorem covarianceStep_eq_coarseCovariance (T A R : Matrix n n 𝕜) :
    covarianceStep T R⁻¹ A⁻¹ = PositiveCoarseGraining.coarseCovariance A R T := by
  simp only [covarianceStep, PositiveCoarseGraining.coarseCovariance,
    Matrix.star_eq_conjTranspose, add_comm]

/-- The prior Schur/Woodbury owner supplies the precision interpretation. -/
theorem covarianceStep_eq_coarsePrecision_inv (T : Matrix n n 𝕜)
    {A R : Matrix n n 𝕜} (hA : A.PosDef) (hR : R.PosDef) :
    covarianceStep T R⁻¹ A⁻¹ = (PositiveCoarseGraining.coarsePrecision A R T)⁻¹ := by
  rw [PositiveCoarseGraining.coarsePrecision_inv T hA hR]
  simp only [covarianceStep, Matrix.star_eq_conjTranspose, add_comm]

end Matrices

end InfoGeometry.OperatorAlgebra.CovarianceTransport
