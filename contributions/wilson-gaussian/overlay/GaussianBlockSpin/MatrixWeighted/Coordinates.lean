/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- The Apache LICENSE for these contributed files is retained as
`LICENSE-InfoGeometry-Apache-2.0` at the package root, together with
`NOTICE-InfoGeometry`; the upstream root CC0 license is separate. -/
import GaussianBlockSpin.MatrixWeighted.Variational
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Euclidean coordinates for matrix-weighted Gaussian elimination

The algebraic operators act on the existing `EuclideanSpace ℝ n` through
Mathlib's `Matrix.toEuclideanLin`. This is the map in the standard orthonormal
basis, so its determinant and quadratic form agree with the matrix determinant
and dot product. The inner product and its canonical volume are unchanged.

These lemmas transport the positive matrix hypotheses, ordered response, and
completed square to the linear-map interface of `GaussianBlockSpin`.
-/

noncomputable section

open Matrix
open WithLp (ofLp)
open scoped RealInnerProductSpace

namespace GaussianBlockSpin.MatrixWeighted

variable {n m l : Type*}
variable [Fintype n] [Fintype m] [Fintype l]
variable [DecidableEq n] [DecidableEq m] [DecidableEq l]

/-- The native Euclidean linear map has the original matrix-vector coordinates. -/
@[simp]
theorem ofLp_toEuclideanLin (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ofLp (M.toEuclideanLin x) = M *ᵥ ofLp x :=
  rfl

/-- The real Euclidean inner product is the original ordered matrix form. -/
theorem inner_toEuclideanLin (M : Matrix m n ℝ)
    (x : EuclideanSpace ℝ m) (y : EuclideanSpace ℝ n) :
    ⟪x, M.toEuclideanLin y⟫ = ofLp x ⬝ᵥ (M *ᵥ ofLp y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin,
    star_trivial, dotProduct_comm]

/-- The standard orthonormal coordinate bridge preserves determinants. -/
@[simp]
theorem det_toEuclideanLin (M : Matrix n n ℝ) :
    LinearMap.det M.toEuclideanLin = M.det :=
  LinearMap.det_toLpLin 2 M

/-- Positive definite matrix precision gives the symmetry required by the Gaussian integral. -/
theorem toEuclideanLin_isSymmetric {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.isHermitian

/-- Strict matrix positivity is strict positivity for the existing Euclidean inner product. -/
theorem inner_toEuclideanLin_pos {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∀ x : EuclideanSpace ℝ n, x ≠ 0 → 0 < ⟪x, M.toEuclideanLin x⟫ := by
  intro x hx
  have hx' : ofLp x ≠ 0 := by
    simpa only [WithLp.ofLp_eq_zero] using hx
  rw [inner_toEuclideanLin]
  simpa only [star_trivial] using hM.dotProduct_mulVec_pos hx'

/-- Positive semidefinite matrix forms remain nonnegative on Euclidean space. -/
theorem inner_toEuclideanLin_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef)
    (x : EuclideanSpace ℝ n) :
    0 ≤ ⟪x, M.toEuclideanLin x⟫ := by
  rw [inner_toEuclideanLin]
  simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg (ofLp x)

/-- Ordered matrix multiplication becomes composition on Euclidean spaces. -/
theorem toEuclideanLin_mul (M : Matrix l m ℝ) (N : Matrix m n ℝ) :
    (M * N).toEuclideanLin = M.toEuclideanLin ∘ₗ N.toEuclideanLin :=
  Matrix.toLpLin_mul_same 2 M N

/-- The coordinate identity is the native identity linear map. -/
@[simp]
theorem toEuclideanLin_one :
    (1 : Matrix n n ℝ).toEuclideanLin = LinearMap.id :=
  Matrix.toLpLin_one 2

/-- Scalar matrix precision agrees with the scalar precision in the original kernel. -/
theorem toEuclideanLin_smul_one (α : ℝ) :
    (α • (1 : Matrix n n ℝ)).toEuclideanLin =
      α • (LinearMap.id : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) := by
  rw [map_smul, toEuclideanLin_one]

/-- Applying the inverse matrix gives an actual right inverse on Euclidean space. -/
theorem toEuclideanLin_apply_inv {M : Matrix n n ℝ} (hM : M.PosDef)
    (x : EuclideanSpace ℝ n) :
    M.toEuclideanLin ((M⁻¹).toEuclideanLin x) = x := by
  let := hM.isUnit.invertible
  have h := congrArg (fun N : Matrix n n ℝ => N.toEuclideanLin x)
    (Matrix.mul_inv_of_invertible M)
  simpa only [toEuclideanLin_mul, LinearMap.comp_apply, toEuclideanLin_one,
    LinearMap.id_apply] using h

/-- Applying the inverse matrix gives an actual left inverse on Euclidean space. -/
theorem toEuclideanLin_inv_apply {M : Matrix n n ℝ} (hM : M.PosDef)
    (x : EuclideanSpace ℝ n) :
    (M⁻¹).toEuclideanLin (M.toEuclideanLin x) = x := by
  let := hM.isUnit.invertible
  have h := congrArg (fun N : Matrix n n ℝ => N.toEuclideanLin x)
    (Matrix.inv_mul_of_invertible M)
  simpa only [toEuclideanLin_mul, LinearMap.comp_apply, toEuclideanLin_one,
    LinearMap.id_apply] using h

variable {A : Matrix n n ℝ} {R : Matrix m m ℝ} (Q : Matrix m n ℝ)

/-- The fine precision is the usual native adjoint-composition expression. -/
theorem toEuclideanLin_finePrecision :
    (finePrecision A R Q).toEuclideanLin =
      A.toEuclideanLin +
        LinearMap.adjoint Q.toEuclideanLin ∘ₗ R.toEuclideanLin ∘ₗ Q.toEuclideanLin := by
  simp only [finePrecision, map_add, toEuclideanLin_mul,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.comp_assoc]

/-- The response applies the inverse fine precision after the ordered adjoint-weighted data. -/
theorem toEuclideanLin_harmonicExtension_apply (y : EuclideanSpace ℝ m) :
    (harmonicExtension A R Q).toEuclideanLin y =
      ((finePrecision A R Q)⁻¹).toEuclideanLin
        (LinearMap.adjoint Q.toEuclideanLin (R.toEuclideanLin y)) := by
  simp only [harmonicExtension, toEuclideanLin_mul, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- The matrix response solves the actual normal equation used in Gaussian integration. -/
theorem finePrecision_harmonicExtension_normalEquation
    (hA : A.PosDef) (hR : R.PosDef) (y : EuclideanSpace ℝ m) :
    (finePrecision A R Q).toEuclideanLin ((harmonicExtension A R Q).toEuclideanLin y) =
      LinearMap.adjoint Q.toEuclideanLin (R.toEuclideanLin y) := by
  have h := congrArg (fun M : Matrix n m ℝ => M.toEuclideanLin y)
    (finePrecision_mul_harmonicExtension Q hA hR)
  simpa only [toEuclideanLin_mul, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using h

/-- The real matrix energy is the same energy in the canonical Euclidean inner products. -/
theorem quadraticEnergy_eq_euclidean (y : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    quadraticEnergy A R Q (ofLp y) (ofLp x) =
      ⟪x, A.toEuclideanLin x⟫ +
        ⟪y - Q.toEuclideanLin x, R.toEuclideanLin (y - Q.toEuclideanLin x)⟫ := by
  simp only [quadraticEnergy, inner_toEuclideanLin, WithLp.ofLp_sub,
    ofLp_toEuclideanLin, star_trivial]

/-- Square completion on the actual spaces carrying the Gaussian integrals. -/
theorem euclidean_quadratic_completion (hA : A.PosDef) (hR : R.PosDef)
    (y : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    ⟪x, A.toEuclideanLin x⟫ +
        ⟪y - Q.toEuclideanLin x, R.toEuclideanLin (y - Q.toEuclideanLin x)⟫ =
      ⟪y, (coarsePrecision A R Q).toEuclideanLin y⟫ +
        ⟪x - (harmonicExtension A R Q).toEuclideanLin y,
          (finePrecision A R Q).toEuclideanLin
            (x - (harmonicExtension A R Q).toEuclideanLin y)⟫ := by
  simpa only [inner_toEuclideanLin, ofLp_toEuclideanLin, WithLp.ofLp_sub,
    star_trivial] using quadratic_completion Q hA hR (ofLp y) (ofLp x)

end GaussianBlockSpin.MatrixWeighted
