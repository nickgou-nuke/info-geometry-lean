/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Analysis.LogDetSelfConcordantBarrier
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic

/-!
# Matrix-to-Spectrum Transport for the Log-Determinant Self-Concordant Barrier

This module formalizes the matrix-to-spectrum transport theorem connecting:
1. The **matrix directional derivatives** of the log-determinant potential:
   - $\nabla^2 \Phi(A)[H, H] = \operatorname{Tr}((A^{-1} H)^2)$
   - $\nabla^3 \Phi(A)[H, H, H] = -2 \operatorname{Tr}((A^{-1} H)^3)$
2. The **conjugated symmetric variation** $B = A^{-1/2} H A^{-1/2}$.
3. The **spectral decomposition** $B = O \operatorname{diag}(\lambda) O^T$ with $O^T O = I$.
4. The **Nesterov–Nemirovski barrier inequality** on the spectrum $\lambda \in \mathbb{R}^n$:
   $$|\nabla^3 \Phi(A)[H, H, H]| \le 2 \left( \nabla^2 \Phi(A)[H, H] \right)^{3/2}$$

All proofs are complete in native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

open Matrix
open BigOperators
open InfoGeometry.Analysis.SelfConcordant

namespace InfoGeometry.Analysis.MatrixSpectral

variable {n : ℕ}

/-! ## 1. Trace Formulas for Diagonal Matrices -/

/-- Trace of the square of a diagonal matrix is the sum of squared diagonal entries. -/
@[simp]
theorem trace_diagonal_sq (ev : Fin n → ℝ) :
    Matrix.trace (Matrix.diagonal ev * Matrix.diagonal ev) = ∑ i : Fin n, (ev i) ^ 2 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp [Matrix.trace_diagonal, pow_two]

/-- Trace of the cube of a diagonal matrix is the sum of cubed diagonal entries. -/
@[simp]
theorem trace_diagonal_cube (ev : Fin n → ℝ) :
    Matrix.trace (Matrix.diagonal ev * Matrix.diagonal ev * Matrix.diagonal ev) = ∑ i : Fin n, (ev i) ^ 3 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp [Matrix.trace_diagonal, pow_succ, mul_assoc]

/-! ## 2. Symmetric Spectral Representation Structure -/

/-- A real symmetric spectral carrier: a matrix $B$ diagonalized by an orthogonal matrix $O$. -/
structure SymmetricSpectralCarrier (n : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  eigenvalues : Fin n → ℝ
  ortho : Matrix (Fin n) (Fin n) ℝ
  ortho_inv : orthoᵀ * ortho = 1
  diagonalized : B = ortho * Matrix.diagonal eigenvalues * orthoᵀ

/-- 🏆 THEOREM: The trace of $B^2$ equals the sum of squared eigenvalues $\sum_i \lambda_i^2$. -/
theorem spectral_trace_sq (C : SymmetricSpectralCarrier n) :
    Matrix.trace (C.B * C.B) = ∑ i : Fin n, (C.eigenvalues i) ^ 2 := by
  have hB := C.diagonalized
  rw [hB]
  let D := Matrix.diagonal C.eigenvalues
  have h_prod : (C.ortho * D * C.orthoᵀ) * (C.ortho * D * C.orthoᵀ) =
                C.ortho * (D * D) * C.orthoᵀ := by
    calc
      (C.ortho * D * C.orthoᵀ) * (C.ortho * D * C.orthoᵀ)
        = C.ortho * D * (C.orthoᵀ * C.ortho) * D * C.orthoᵀ := by
          simp only [Matrix.mul_assoc]
      _ = C.ortho * D * 1 * D * C.orthoᵀ := by
          rw [C.ortho_inv]
      _ = C.ortho * (D * D) * C.orthoᵀ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [h_prod]
  have h_cyc : Matrix.trace (C.ortho * (D * D) * C.orthoᵀ) = Matrix.trace (D * D) := by
    rw [Matrix.trace_mul_comm (C.ortho * (D * D)) C.orthoᵀ]
    have h_assoc : C.orthoᵀ * (C.ortho * (D * D)) = (C.orthoᵀ * C.ortho) * (D * D) := by
      simp only [Matrix.mul_assoc]
    rw [h_assoc, C.ortho_inv, Matrix.one_mul]
  rw [h_cyc]
  exact trace_diagonal_sq C.eigenvalues

/-- 🏆 THEOREM: The trace of $B^3$ equals the sum of cubed eigenvalues $\sum_i \lambda_i^3$. -/
theorem spectral_trace_cube (C : SymmetricSpectralCarrier n) :
    Matrix.trace (C.B * C.B * C.B) = ∑ i : Fin n, (C.eigenvalues i) ^ 3 := by
  have hB := C.diagonalized
  rw [hB]
  let D := Matrix.diagonal C.eigenvalues
  have h_prod3 : (C.ortho * D * C.orthoᵀ) * (C.ortho * D * C.orthoᵀ) * (C.ortho * D * C.orthoᵀ) =
                 C.ortho * (D * D * D) * C.orthoᵀ := by
    calc
      (C.ortho * D * C.orthoᵀ) * (C.ortho * D * C.orthoᵀ) * (C.ortho * D * C.orthoᵀ)
        = (C.ortho * D * (C.orthoᵀ * C.ortho) * D * (C.orthoᵀ * C.ortho) * D) * C.orthoᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (C.ortho * D * 1 * D * 1 * D) * C.orthoᵀ := by
          rw [C.ortho_inv]
      _ = C.ortho * (D * D * D) * C.orthoᵀ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [h_prod3]
  have h_cyc : Matrix.trace (C.ortho * (D * D * D) * C.orthoᵀ) = Matrix.trace (D * D * D) := by
    rw [Matrix.trace_mul_comm (C.ortho * (D * D * D)) C.orthoᵀ]
    have h_assoc : C.orthoᵀ * (C.ortho * (D * D * D)) = (C.orthoᵀ * C.ortho) * (D * D * D) := by
      simp only [Matrix.mul_assoc]
    rw [h_assoc, C.ortho_inv, Matrix.one_mul]
  rw [h_cyc]
  exact trace_diagonal_cube C.eigenvalues

/-- Exact squared sum-of-cubes inequality: `(∑ ev_i³)² ≤ (∑ ev_i²)³`. -/
theorem spectral_sum_cube_sq_le_sum_sq_cube (n : ℕ) (ev : Fin n → ℝ) :
    (∑ i : Fin n, (ev i) ^ 3) ^ 2 ≤ (∑ i : Fin n, (ev i) ^ 2) ^ 3 := by
  have h_abs := spectral_sum_cube_le_sum_sq_three_halves ev
  have h_sq_nonneg : 0 ≤ ∑ i : Fin n, (ev i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (ev i))
  have h_rpow : ((∑ i : Fin n, (ev i) ^ 2) ^ (3 / 2 : ℝ)) ^ 2 = (∑ i : Fin n, (ev i) ^ 2) ^ 3 := by
    rw [rpow_three_halves_eq_mul_sqrt _ h_sq_nonneg]
    calc
      ((∑ i : Fin n, (ev i) ^ 2) * Real.sqrt (∑ i : Fin n, (ev i) ^ 2)) ^ 2
        = (∑ i : Fin n, (ev i) ^ 2) ^ 2 * (Real.sqrt (∑ i : Fin n, (ev i) ^ 2)) ^ 2 := mul_pow _ _ 2
      _ = (∑ i : Fin n, (ev i) ^ 2) ^ 2 * (∑ i : Fin n, (ev i) ^ 2) := by
        rw [Real.sq_sqrt h_sq_nonneg]
      _ = (∑ i : Fin n, (ev i) ^ 2) ^ 3 := by ring
  have h_sq_le : (|∑ i : Fin n, (ev i) ^ 3|) ^ 2 ≤ (((∑ i : Fin n, (ev i) ^ 2) ^ (3 / 2 : ℝ))) ^ 2 := by
    have h_lhs_nonneg : 0 ≤ |∑ i : Fin n, (ev i) ^ 3| := abs_nonneg _
    have h_rhs_nonneg : 0 ≤ (∑ i : Fin n, (ev i) ^ 2) ^ (3 / 2 : ℝ) := by
      rw [rpow_three_halves_eq_mul_sqrt _ h_sq_nonneg]
      exact mul_nonneg h_sq_nonneg (Real.sqrt_nonneg _)
    exact sq_le_sq.mpr (by rw [abs_of_nonneg h_lhs_nonneg, abs_of_nonneg h_rhs_nonneg]; exact h_abs)
  rw [sq_abs, h_rpow] at h_sq_le
  exact h_sq_le

/-! ## 3. Conjugated Variation Structure -/

/-- Data of a matrix variation $H$ conjugated by $A^{-1/2}$. -/
structure MatrixVariationConjugation (n : ℕ) where
  A_inv_sqrt : Matrix (Fin n) (Fin n) ℝ
  H : Matrix (Fin n) (Fin n) ℝ
  A_inv : Matrix (Fin n) (Fin n) ℝ
  inv_sqrt_sq : A_inv_sqrt * A_inv_sqrt = A_inv
  B : Matrix (Fin n) (Fin n) ℝ
  B_def : B = A_inv_sqrt * H * A_inv_sqrt

/-- 🏆 THEOREM: The Hessian quadratic form $\operatorname{Tr}((A^{-1} H)^2)$ equals $\operatorname{Tr}(B^2)$. -/
theorem trace_inv_H_sq_eq_trace_B_sq (V : MatrixVariationConjugation n) :
    Matrix.trace ((V.A_inv * V.H) * (V.A_inv * V.H)) = Matrix.trace (V.B * V.B) := by
  have h_A : V.A_inv = V.A_inv_sqrt * V.A_inv_sqrt := V.inv_sqrt_sq.symm
  rw [h_A]
  have h_lhs : (V.A_inv_sqrt * V.A_inv_sqrt * V.H) * (V.A_inv_sqrt * V.A_inv_sqrt * V.H) =
               V.A_inv_sqrt * (V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H) := by
    simp only [Matrix.mul_assoc]
  rw [h_lhs]
  have h_cyc : Matrix.trace (V.A_inv_sqrt * (V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H)) =
               Matrix.trace ((V.A_inv_sqrt * V.H * V.A_inv_sqrt) * (V.A_inv_sqrt * V.H * V.A_inv_sqrt)) := by
    have h_assoc : (V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H) * V.A_inv_sqrt =
                   (V.A_inv_sqrt * V.H * V.A_inv_sqrt) * (V.A_inv_sqrt * V.H * V.A_inv_sqrt) := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm V.A_inv_sqrt, h_assoc]
  rw [h_cyc, ← V.B_def]

/-- 🏆 THEOREM: The 3rd derivative trace $\operatorname{Tr}((A^{-1} H)^3)$ equals $\operatorname{Tr}(B^3)$. -/
theorem trace_inv_H_cube_eq_trace_B_cube (V : MatrixVariationConjugation n) :
    Matrix.trace ((V.A_inv * V.H) * (V.A_inv * V.H) * (V.A_inv * V.H)) =
      Matrix.trace (V.B * V.B * V.B) := by
  have h_A : V.A_inv = V.A_inv_sqrt * V.A_inv_sqrt := V.inv_sqrt_sq.symm
  rw [h_A]
  have h_lhs : (V.A_inv_sqrt * V.A_inv_sqrt * V.H) * (V.A_inv_sqrt * V.A_inv_sqrt * V.H) * (V.A_inv_sqrt * V.A_inv_sqrt * V.H) =
               V.A_inv_sqrt * (V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H) := by
    simp only [Matrix.mul_assoc]
  rw [h_lhs]
  have h_cyc : Matrix.trace (V.A_inv_sqrt * (V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H)) =
               Matrix.trace ((V.A_inv_sqrt * V.H * V.A_inv_sqrt) * (V.A_inv_sqrt * V.H * V.A_inv_sqrt) * (V.A_inv_sqrt * V.H * V.A_inv_sqrt)) := by
    have h_assoc : (V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H * V.A_inv_sqrt * V.A_inv_sqrt * V.H) * V.A_inv_sqrt =
                   (V.A_inv_sqrt * V.H * V.A_inv_sqrt) * (V.A_inv_sqrt * V.H * V.A_inv_sqrt) * (V.A_inv_sqrt * V.H * V.A_inv_sqrt) := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm V.A_inv_sqrt, h_assoc]
  rw [h_cyc, ← V.B_def]

/-! ## 4. Explicit Matrix-to-Spectrum Equality Theorems -/

/-- 🏆 THEOREM: The Hessian quadratic form $\nabla^2 \Phi(A)[H, H]$ equals the sum of squared eigenvalues $\sum_i \lambda_i^2$. -/
theorem hessianQuad_eq_sum_eigenvalues_sq
    (V : MatrixVariationConjugation n)
    (C : SymmetricSpectralCarrier n)
    (h_carrier : V.B = C.B) :
    hessianQuad V.A_inv V.H = ∑ i : Fin n, (C.eigenvalues i) ^ 2 := by
  dsimp [hessianQuad]
  rw [trace_inv_H_sq_eq_trace_B_sq V, h_carrier, spectral_trace_sq C]

/-- 🏆 THEOREM: The 3rd directional derivative $\nabla^3 \Phi(A)[H, H, H]$ equals $-2 \sum_i \lambda_i^3$. -/
theorem thirdDerivPhi_eq_neg_two_sum_eigenvalues_cube
    (V : MatrixVariationConjugation n)
    (C : SymmetricSpectralCarrier n)
    (h_carrier : V.B = C.B) :
    thirdDerivPhi V.A_inv V.H = - 2 * ∑ i : Fin n, (C.eigenvalues i) ^ 3 := by
  dsimp [thirdDerivPhi]
  rw [trace_inv_H_cube_eq_trace_B_cube V, h_carrier, spectral_trace_cube C]

/-- 🏆 THEOREM: The absolute 3rd derivative $|\nabla^3 \Phi(A)[H, H, H]|$ equals $2 |\sum_i \lambda_i^3|$. -/
theorem thirdDerivPhi_abs_eq_two_mul_abs_sum_eigenvalues_cube
    (V : MatrixVariationConjugation n)
    (C : SymmetricSpectralCarrier n)
    (h_carrier : V.B = C.B) :
    |thirdDerivPhi V.A_inv V.H| = 2 * |∑ i : Fin n, (C.eigenvalues i) ^ 3| := by
  rw [thirdDerivPhi_eq_neg_two_sum_eigenvalues_cube V C h_carrier]
  rw [abs_mul, abs_neg, abs_two]

/-! ## 5. Master Matrix-to-Spectrum Self-Concordance Barrier Theorem -/

/-- 🏆 MASTER THEOREM: Full matrix-to-spectrum transport of the Nesterov–Nemirovski self-concordance inequality. -/
theorem matrix_self_concordance_barrier_bound
    (V : MatrixVariationConjugation n)
    (C : SymmetricSpectralCarrier n)
    (h_carrier : V.B = C.B) :
    |thirdDerivPhi V.A_inv V.H| ≤ 2 * (hessianQuad V.A_inv V.H) ^ (3 / 2 : ℝ) := by
  rw [thirdDerivPhi_abs_eq_two_mul_abs_sum_eigenvalues_cube V C h_carrier,
      hessianQuad_eq_sum_eigenvalues_sq V C h_carrier]
  have h_spec := spectral_sum_cube_le_sum_sq_three_halves C.eigenvalues
  nlinarith

/-! ## 6. Canonical Spectral Matrix Variation Structure (Hypothesis-Free) -/

/-- A canonical spectral matrix variation: bundles the matrix variation data and its orthogonal
spectral decomposition together, guaranteeing $B = A^{-1/2} H A^{-1/2} = O \operatorname{diag}(\lambda) O^T$
identically without requiring external alignment hypotheses. -/
structure CanonicalSpectralMatrixVariation (n : ℕ) where
  A_inv_sqrt : Matrix (Fin n) (Fin n) ℝ
  H : Matrix (Fin n) (Fin n) ℝ
  A_inv : Matrix (Fin n) (Fin n) ℝ
  inv_sqrt_sq : A_inv_sqrt * A_inv_sqrt = A_inv
  eigenvalues : Fin n → ℝ
  ortho : Matrix (Fin n) (Fin n) ℝ
  ortho_inv : orthoᵀ * ortho = 1
  diagonalized : A_inv_sqrt * H * A_inv_sqrt = ortho * Matrix.diagonal eigenvalues * orthoᵀ

namespace CanonicalSpectralMatrixVariation

variable {n : ℕ}

/-- Projection to `MatrixVariationConjugation`. -/
def toConjugation (V : CanonicalSpectralMatrixVariation n) : MatrixVariationConjugation n where
  A_inv_sqrt := V.A_inv_sqrt
  H := V.H
  A_inv := V.A_inv
  inv_sqrt_sq := V.inv_sqrt_sq
  B := V.A_inv_sqrt * V.H * V.A_inv_sqrt
  B_def := rfl

/-- Projection to `SymmetricSpectralCarrier`. -/
def toCarrier (V : CanonicalSpectralMatrixVariation n) : SymmetricSpectralCarrier n where
  B := V.A_inv_sqrt * V.H * V.A_inv_sqrt
  eigenvalues := V.eigenvalues
  ortho := V.ortho
  ortho_inv := V.ortho_inv
  diagonalized := V.diagonalized

/-- Definitional match of the conjugated matrix and spectral carrier matrix. -/
@[simp] theorem carrier_match (V : CanonicalSpectralMatrixVariation n) :
    V.toConjugation.B = V.toCarrier.B := rfl

/-- 🏆 THEOREM: Unconditional Hessian quadratic form eigenvalue equality. -/
theorem hessianQuad_eq (V : CanonicalSpectralMatrixVariation n) :
    hessianQuad V.A_inv V.H = ∑ i : Fin n, (V.eigenvalues i) ^ 2 :=
  hessianQuad_eq_sum_eigenvalues_sq V.toConjugation V.toCarrier V.carrier_match

/-- 🏆 THEOREM: Unconditional 3rd directional derivative eigenvalue equality. -/
theorem thirdDerivPhi_eq (V : CanonicalSpectralMatrixVariation n) :
    thirdDerivPhi V.A_inv V.H = - 2 * ∑ i : Fin n, (V.eigenvalues i) ^ 3 :=
  thirdDerivPhi_eq_neg_two_sum_eigenvalues_cube V.toConjugation V.toCarrier V.carrier_match

/-- 🏆 THEOREM: Unconditional absolute 3rd derivative eigenvalue equality. -/
theorem thirdDerivPhi_abs_eq (V : CanonicalSpectralMatrixVariation n) :
    |thirdDerivPhi V.A_inv V.H| = 2 * |∑ i : Fin n, (V.eigenvalues i) ^ 3| :=
  thirdDerivPhi_abs_eq_two_mul_abs_sum_eigenvalues_cube V.toConjugation V.toCarrier V.carrier_match

/-- 🏆 THEOREM: Unconditional Nesterov-Nemirovski barrier bound on matrix variations. -/
theorem matrix_self_concordance_barrier_bound (V : CanonicalSpectralMatrixVariation n) :
    |thirdDerivPhi V.A_inv V.H| ≤ 2 * (hessianQuad V.A_inv V.H) ^ (3 / 2 : ℝ) :=
  InfoGeometry.Analysis.MatrixSpectral.matrix_self_concordance_barrier_bound V.toConjugation V.toCarrier V.carrier_match

/-- 🏆 THEOREM: Unconditional algebraic squared self-concordance bound on matrix variations. -/
theorem matrix_self_concordance_sq_bound (V : CanonicalSpectralMatrixVariation n) :
    (thirdDerivPhi V.A_inv V.H) ^ 2 ≤ 4 * (hessianQuad V.A_inv V.H) ^ 3 := by
  rw [V.thirdDerivPhi_eq, V.hessianQuad_eq]
  have h_cube_sq := spectral_sum_cube_sq_le_sum_sq_cube n V.eigenvalues
  calc
    (- 2 * ∑ i : Fin n, (V.eigenvalues i) ^ 3) ^ 2 = 4 * (∑ i : Fin n, (V.eigenvalues i) ^ 3) ^ 2 := by ring
    _ ≤ 4 * (∑ i : Fin n, (V.eigenvalues i) ^ 2) ^ 3 := by linarith

/-! ### Automatic Canonical Constructors -/

/-- Explicit construction of a spectral carrier for any diagonal matrix. -/
def diagonalCarrier (d : Fin n → ℝ) : SymmetricSpectralCarrier n where
  B := Matrix.diagonal d
  eigenvalues := d
  ortho := 1
  ortho_inv := by simp
  diagonalized := by simp

/-- Canonical constructor for any diagonal SPD matrix and variation:
constructs the spectral carrier automatically with $\lambda_i = a_i^{-1} h_i$. -/
def fromDiagonal (a_inv_sqrt h : Fin n → ℝ) : CanonicalSpectralMatrixVariation n where
  A_inv_sqrt := Matrix.diagonal a_inv_sqrt
  H := Matrix.diagonal h
  A_inv := Matrix.diagonal (fun i => (a_inv_sqrt i) ^ 2)
  inv_sqrt_sq := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [pow_two]
  eigenvalues := fun i => a_inv_sqrt i * h i * a_inv_sqrt i
  ortho := 1
  ortho_inv := by simp
  diagonalized := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp

/-- Canonical constructor from any aligned conjugation and spectral carrier pair. -/
def ofConjugationAndCarrier (V : MatrixVariationConjugation n) (C : SymmetricSpectralCarrier n)
    (h_carrier : V.B = C.B) : CanonicalSpectralMatrixVariation n where
  A_inv_sqrt := V.A_inv_sqrt
  H := V.H
  A_inv := V.A_inv
  inv_sqrt_sq := V.inv_sqrt_sq
  eigenvalues := C.eigenvalues
  ortho := C.ortho
  ortho_inv := C.ortho_inv
  diagonalized := by
    have hV := V.B_def
    have hC := C.diagonalized
    rw [← hV, h_carrier, hC]

/-- Canonical constructor for scalar variations ($n$ identical scalar modes). -/
def fromScalar (n : ℕ) (a_inv_sqrt h : ℝ) : CanonicalSpectralMatrixVariation n :=
  fromDiagonal (fun _ => a_inv_sqrt) (fun _ => h)

/-- 🏆 UNCONDITIONAL THEOREM: Self-concordance barrier inequality on any diagonal SPD matrix variation,
with explicitly constructed spectral carrier. -/
theorem diagonal_matrix_self_concordance_barrier_bound
    (a_inv_sqrt h : Fin n → ℝ) :
    let V := fromDiagonal a_inv_sqrt h
    |thirdDerivPhi V.A_inv V.H| ≤ 2 * (hessianQuad V.A_inv V.H) ^ (3 / 2 : ℝ) := by
  intro V
  exact V.matrix_self_concordance_barrier_bound

end CanonicalSpectralMatrixVariation
