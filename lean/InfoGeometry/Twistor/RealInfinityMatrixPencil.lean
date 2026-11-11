/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SignedPermutation
import InfoGeometry.OperatorAlgebra.ChiralCouplingOperators
import InfoGeometry.Quantum.NeutralKreinMajoranaFrame

/-!
# A real infinity-form pencil in the native doubled matrix carrier

The spinor alternating matrix is the existing `Cl11Matrix.Eminus`; the
symmetric exchange matrix is the existing `kreinMetric 2`. The two projected
alternating matrices are degenerate. Multiplication by the exchange matrix
produces a distinct endomorphism whose square is a scalar matrix.

The parameter is a real scalar, hence central in this matrix algebra. The
generic noncommuting-block identity remains `coupling_square`, with its two
ordered products. No spacetime curvature or physical mass is constructed.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealInfinityMatrixPencil

open Matrix
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.OperatorAlgebra.ChiralCouplingOperators
open InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open scoped Matrix

/-- The lower-spinor alternating matrix on the existing doubled real carrier. -/
def infinityLowerMatrix : DoubledMat4R :=
  Matrix.fromBlocks 0 0 0 Eminus

/-- The complementary upper-spinor alternating matrix. This is a matrix of a
bilinear form; it is not identified with a dual-to-vector infinity bivector. -/
def infinityUpperMatrix : DoubledMat4R :=
  Matrix.fromBlocks Eminus 0 0 0

/-- A real scalar pencil of the two complementary alternating forms. -/
def infinityMatrixPencil (Λ : ℝ) : DoubledMat4R :=
  infinityLowerMatrix + Λ • infinityUpperMatrix

/-- Raising the second argument using the fixed symmetric exchange matrix. -/
def raisedInfinityMatrix (Λ : ℝ) : DoubledMat4R :=
  kreinMetric 2 * infinityMatrixPencil Λ

theorem infinityLowerMatrix_transpose :
    infinityLowerMatrixᵀ = -infinityLowerMatrix := by
  have hΩ : Eminusᵀ = -Eminus :=
    InfoGeometry.Clifford.SignedPermutation.e2_transpose
  simp only [infinityLowerMatrix, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, hΩ, Matrix.fromBlocks_neg, neg_zero]

theorem infinityUpperMatrix_transpose :
    infinityUpperMatrixᵀ = -infinityUpperMatrix := by
  have hΩ : Eminusᵀ = -Eminus :=
    InfoGeometry.Clifford.SignedPermutation.e2_transpose
  simp only [infinityUpperMatrix, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, hΩ, Matrix.fromBlocks_neg, neg_zero]

theorem infinityLowerMatrix_mul_upper :
    infinityLowerMatrix * infinityUpperMatrix = 0 := by
  simp [infinityLowerMatrix, infinityUpperMatrix, Matrix.fromBlocks_multiply]

theorem infinityUpperMatrix_mul_lower :
    infinityUpperMatrix * infinityLowerMatrix = 0 := by
  simp [infinityLowerMatrix, infinityUpperMatrix, Matrix.fromBlocks_multiply]

/-- The complementary blocks recover the full diagonal spinor form. -/
theorem infinityUpperMatrix_add_lower :
    infinityUpperMatrix + infinityLowerMatrix =
      Matrix.fromBlocks Eminus 0 0 Eminus := by
  simp [infinityLowerMatrix, infinityUpperMatrix, Matrix.fromBlocks_add]

theorem infinityUpperMatrix_sub_lower :
    infinityUpperMatrix - infinityLowerMatrix =
      Matrix.fromBlocks Eminus 0 0 (-Eminus) := by
  simp [infinityLowerMatrix, infinityUpperMatrix, sub_eq_add_neg,
    Matrix.fromBlocks_add, Matrix.fromBlocks_neg]

/-- The upper form is cut out by the already-owned Peirce projection. -/
theorem infinityUpperMatrix_eq_projection_mul :
    infinityUpperMatrix =
      leftProjection (R := ℝ) (m := Fin 2) (n := Fin 2) *
        (infinityUpperMatrix + infinityLowerMatrix) := by
  rw [infinityUpperMatrix_add_lower]
  simp [leftProjection, infinityUpperMatrix, Matrix.fromBlocks_multiply]

/-- The complementary Peirce projection cuts out the lower form. -/
theorem infinityLowerMatrix_eq_complement_mul :
    infinityLowerMatrix =
      ((1 : DoubledMat4R) - leftProjection (R := ℝ) (m := Fin 2) (n := Fin 2)) *
        (infinityUpperMatrix + infinityLowerMatrix) := by
  rw [sub_mul, one_mul, ← infinityUpperMatrix_eq_projection_mul]
  abel

theorem infinityMatrixPencil_eq_blocks (Λ : ℝ) :
    infinityMatrixPencil Λ = Matrix.fromBlocks (Λ • Eminus) 0 0 Eminus := by
  simp [infinityMatrixPencil, infinityLowerMatrix, infinityUpperMatrix,
    Matrix.fromBlocks_smul, Matrix.fromBlocks_add]

theorem infinityMatrixPencil_transpose (Λ : ℝ) :
    (infinityMatrixPencil Λ)ᵀ = -infinityMatrixPencil Λ := by
  have hΩ : Eminusᵀ = -Eminus :=
    InfoGeometry.Clifford.SignedPermutation.e2_transpose
  rw [infinityMatrixPencil_eq_blocks]
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, hΩ]

/-- Metric raising exchanges the diagonal form blocks into chiral operators. -/
theorem raisedInfinityMatrix_eq_chiral (Λ : ℝ) :
    raisedInfinityMatrix Λ = chiral Eminus (Λ • Eminus) := by
  rw [raisedInfinityMatrix, infinityMatrixPencil_eq_blocks]
  simp [kreinMetric, chiral, Matrix.fromBlocks_multiply]

/-- Lowering with the same involution returns the alternating matrix. -/
theorem metric_mul_raisedInfinityMatrix (Λ : ℝ) :
    kreinMetric 2 * raisedInfinityMatrix Λ = infinityMatrixPencil Λ := by
  rw [raisedInfinityMatrix, ← mul_assoc]
  simp only [kreinMetric_is_neutral, exchange_sq, one_mul]

/-- The raised operator is skew for the exchange pairing, not necessarily for
the positive coordinate dot product. -/
theorem raisedInfinityMatrix_metric_skew (Λ : ℝ) :
    (raisedInfinityMatrix Λ)ᵀ * kreinMetric 2 =
      -(kreinMetric 2 * raisedInfinityMatrix Λ) := by
  calc
    (raisedInfinityMatrix Λ)ᵀ * kreinMetric 2 =
        (kreinMetric 2 * raisedInfinityMatrix Λ)ᵀ := by
      rw [Matrix.transpose_mul, kreinMetric_transpose]
    _ = (infinityMatrixPencil Λ)ᵀ := by
      rw [metric_mul_raisedInfinityMatrix]
    _ = -infinityMatrixPencil Λ := infinityMatrixPencil_transpose Λ
    _ = -(kreinMetric 2 * raisedInfinityMatrix Λ) := by
      rw [metric_mul_raisedInfinityMatrix]

/-- The exact finite square law follows from the existing ordered block square
and the existing spinor Clifford relation. -/
theorem raisedInfinityMatrix_sq (Λ : ℝ) :
    raisedInfinityMatrix Λ * raisedInfinityMatrix Λ =
      (-Λ) • (1 : DoubledMat4R) := by
  have hΩsq : Eminus * Eminus = -(1 : Mat2) := by
    simpa using Eminus_sq
  rw [raisedInfinityMatrix_eq_chiral, coupling_square]
  calc
    Matrix.fromBlocks (Eminus * (Λ • Eminus)) 0 0 ((Λ • Eminus) * Eminus) =
        Matrix.fromBlocks ((-Λ) • (1 : Mat2)) 0 0 ((-Λ) • (1 : Mat2)) := by
      simp [mul_smul_comm, smul_mul_assoc, hΩsq]
    _ = (-Λ) • Matrix.fromBlocks (1 : Mat2) 0 0 (1 : Mat2) := by
      rw [Matrix.fromBlocks_smul]
      simp only [smul_zero]
    _ = (-Λ) • (1 : DoubledMat4R) := by
      rw [Matrix.fromBlocks_one]

/-- The same identity acts on the actual four-dimensional vector carrier. -/
theorem raisedInfinityMatrix_mulVec_twice (Λ : ℝ) (v : Carrier 2 → ℝ) :
    raisedInfinityMatrix Λ *ᵥ (raisedInfinityMatrix Λ *ᵥ v) = (-Λ) • v := by
  rw [Matrix.mulVec_mulVec, raisedInfinityMatrix_sq,
    Matrix.smul_mulVec, Matrix.one_mulVec]

@[simp] theorem raisedInfinityMatrix_flat_sq :
    raisedInfinityMatrix 0 * raisedInfinityMatrix 0 = 0 := by
  simpa using raisedInfinityMatrix_sq 0

/-- The upper-right unit entry remains nonzero even at the flat parameter. -/
theorem raisedInfinityMatrix_ne_zero (Λ : ℝ) : raisedInfinityMatrix Λ ≠ 0 := by
  intro h
  have h01 := congrArg
    (fun A : DoubledMat4R => A (Sum.inl 0) (Sum.inr 1)) h
  norm_num [raisedInfinityMatrix_eq_chiral, chiral, Eminus] at h01

/-- The existing idempotency defect has this exact polynomial value. -/
theorem raisedInfinityMatrix_defect (Λ : ℝ) :
    InfoGeometry.Core.IdempotencyDefect.defect (raisedInfinityMatrix Λ) =
      (-Λ) • (1 : DoubledMat4R) - raisedInfinityMatrix Λ := by
  rw [InfoGeometry.Core.IdempotencyDefect.defect, raisedInfinityMatrix_sq]

/-- Its fixed nonzero upper-right entry rules out idempotence at every parameter. -/
theorem raisedInfinityMatrix_defect_ne_zero (Λ : ℝ) :
    InfoGeometry.Core.IdempotencyDefect.defect (raisedInfinityMatrix Λ) ≠ 0 := by
  rw [raisedInfinityMatrix_defect]
  intro h
  have h01 := congrArg
    (fun A : DoubledMat4R => A (Sum.inl 0) (Sum.inr 1)) h
  norm_num [raisedInfinityMatrix_eq_chiral, chiral, Eminus] at h01

/-- This equivalence uses the nontrivial real scalar carrier. -/
theorem raisedInfinityMatrix_sq_eq_zero_iff (Λ : ℝ) :
    raisedInfinityMatrix Λ * raisedInfinityMatrix Λ = 0 ↔ Λ = 0 := by
  rw [raisedInfinityMatrix_sq]
  constructor
  · intro h
    have h00 := congrArg
      (fun A : DoubledMat4R => A (Sum.inl 0) (Sum.inl 0)) h
    simpa using h00
  · rintro rfl
    simp

/-- For a nonzero real parameter, the inverse is the displayed scalar multiple. -/
theorem raisedInfinityMatrix_mul_scaled_inverse (Λ : ℝ) (hΛ : Λ ≠ 0) :
    raisedInfinityMatrix Λ * ((-Λ⁻¹) • raisedInfinityMatrix Λ) = 1 := by
  rw [mul_smul_comm, raisedInfinityMatrix_sq, smul_smul]
  simp [hΛ]

theorem scaled_inverse_mul_raisedInfinityMatrix (Λ : ℝ) (hΛ : Λ ≠ 0) :
    ((-Λ⁻¹) • raisedInfinityMatrix Λ) * raisedInfinityMatrix Λ = 1 := by
  rw [smul_mul_assoc, raisedInfinityMatrix_sq, smul_smul]
  simp [hΛ]

end InfoGeometry.Twistor.RealInfinityMatrixPencil
