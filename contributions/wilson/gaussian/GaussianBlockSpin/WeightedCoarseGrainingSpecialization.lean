/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
import GaussianBlockSpin.WeightedEffectiveForm
import GaussianBlockSpin.Convolution
import Mathlib.Tactic.Field

/-!
# Scalar composition and weighted-adjoint conventions

The covariance and precision of the matrix elimination specialize to the exact
coefficient of the existing block-kernel convolution theorem, with its parameter
`s` retained. The weighted-adjoint statements use explicit weights;
they do not assert an unproved identification with a particular lattice operator.
-/

noncomputable section

namespace GaussianBlockSpin.WeightedCoarseGraining

open Matrix MeasureTheory
open scoped RealInnerProductSpace

section ScalarComposition

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private theorem inv_scalar_one (a : ℝ) (ha : a ≠ 0) :
    (a • (1 : Matrix n n ℝ))⁻¹ = a⁻¹ • 1 := by
  apply Matrix.inv_eq_right_inv
  simp [smul_smul, ha]

/-- Scalar noise precisions give the covariance coefficient used by
`integral_blockKernel_mul_blockKernel`, including its coisometry factor `s`. -/
theorem coarseCovariance_scalar_eq (Q : Matrix m n ℝ) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hQ : Q * Qᴴ = s • (1 : Matrix m m ℝ)) :
    coarseCovariance (β • (1 : Matrix n n ℝ)) (α • (1 : Matrix m m ℝ)) Q =
      ((β + s * α) / (α * β)) • (1 : Matrix m m ℝ) := by
  rw [coarseCovariance, inv_scalar_one α hα.ne', inv_scalar_one β hβ.ne',
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ, smul_smul, ← add_smul]
  congr 1
  field [hα.ne', hβ.ne']

/-- The native Schur complement specializes to the existing scalar kernel
composition coefficient. No normalization `s = 1` is imposed. -/
theorem coarsePrecision_scalar_eq (Q : Matrix m n ℝ) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s)
    (hQ : Q * Qᴴ = s • (1 : Matrix m m ℝ)) :
    coarsePrecision (β • (1 : Matrix n n ℝ)) (α • (1 : Matrix m m ℝ)) Q =
      (α * β / (β + s * α)) • (1 : Matrix m m ℝ) := by
  rw [← coarseCovariance_inv Q (Matrix.PosDef.one.smul hβ)
    (Matrix.PosDef.one.smul hα), coarseCovariance_scalar_eq Q hα hβ hQ]
  apply Matrix.inv_eq_right_inv
  have hden : β + s * α ≠ 0 := (by positivity : 0 < β + s * α).ne'
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  have hc : (β + s * α) / (α * β) * (α * β / (β + s * α)) = 1 := by
    field [hden, hα.ne', hβ.ne']
  rw [mul_comm (α * β / (β + s * α)) ((β + s * α) / (α * β)), hc, one_smul]

/-- The matrix coisometry hypothesis is exactly the hypothesis of the existing
Euclidean block-kernel convolution theorem. This is an integration-level
specialization, with both averaging maps retained in their original order. -/
theorem integral_blockKernel_mul_blockKernel_matrix {l : Type*} [Fintype l]
    [DecidableEq l] (Q : Matrix m n ℝ) (P : Matrix n l ℝ) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s)
    (hQ : Q * Qᴴ = s • (1 : Matrix m m ℝ))
    (ψ : EuclideanSpace ℝ m) (φ : EuclideanSpace ℝ l) :
    ∫ θ : EuclideanSpace ℝ n,
        blockKernel α hα Q.toEuclideanLin ψ θ *
          blockKernel β hβ P.toEuclideanLin θ φ =
      blockKernel (α * β / (β + s * α)) (convCoeff_pos hα hβ hs)
        (Q * P).toEuclideanLin ψ φ := by
  have hQ' : Q.toEuclideanLin ∘ₗ LinearMap.adjoint Q.toEuclideanLin =
      s • LinearMap.id := by
    have h := congrArg (fun M : Matrix m m ℝ => M.toEuclideanLin) hQ
    simpa only [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      map_smul, Matrix.toEuclideanLin, Matrix.toLpLin_one] using h
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
    integral_blockKernel_mul_blockKernel hα hβ hs Q.toEuclideanLin
      P.toEuclideanLin hQ' ψ φ

end ScalarComposition

section WeightedAdjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- For positive weights, this identity identifies the adjoint for the scaled
inner products as `(v / u) • adjoint Q`. The algebraic identity needs only
`u ≠ 0`; no particular lattice units are imposed. -/
theorem weighted_adjoint_inner (Q : E →ₗ[ℝ] F) {u v : ℝ}
    (hu : u ≠ 0) (x : E) (y : F) :
    u * ⟪x, (v / u) • LinearMap.adjoint Q y⟫ = v * ⟪Q x, y⟫ := by
  rw [real_inner_smul_right, LinearMap.adjoint_inner_right]
  field [hu]

end WeightedAdjoint

section WeightedMatrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- If the chosen adjoint is `w • Qᴴ`, the precision weight `(α*w) • R`
equals `α` times the weighted-adjoint term. The scale `w` occurs once. -/
theorem finePrecision_weighted_adjoint (A : Matrix n n ℝ) (R : Matrix m m ℝ)
    (Q : Matrix m n ℝ) (α w : ℝ) :
    finePrecision A ((α * w) • R) Q = A + α • ((w • Qᴴ) * R * Q) := by
  simp only [finePrecision, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

omit [Fintype n] [DecidableEq n] in
/-- With identity coarse weight, the weighted block matrix already contains
`w`; multiplying it by `α*w` would count the lattice scale twice. -/
theorem finePrecision_weighted_identity (A : Matrix n n ℝ)
    (Q : Matrix m n ℝ) (α w : ℝ) :
    finePrecision A ((α * w) • (1 : Matrix m m ℝ)) Q =
      A + α • ((w • Qᴴ) * Q) := by
  simpa only [Matrix.mul_one] using finePrecision_weighted_adjoint A 1 Q α w

end WeightedMatrix

end GaussianBlockSpin.WeightedCoarseGraining
