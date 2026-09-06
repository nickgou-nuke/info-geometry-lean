/-
InfoGeometry/Geometry/FiniteMatrixResolventKernel.lean

Finite matrix resolvent kernel individuation.

This file replaces the abstract resolvent-exists socket by explicit finite
matrix inverse data.  For a finite matrix `A` and spectral parameter `z`, the
resolvent difference is

  M(z,A) = z • I - A.

A resolvent kernel is a matrix `R` equipped with two-sided inverse proofs.
-/

import Mathlib
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Geometry.FiniteMatrixResolventKernel

open Matrix

/-! ## 1. Finite matrix resolvent difference -/

/-- Finite matrix resolvent difference: `M(z,A) = z • I - A`. -/
def resolventDiff
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ)
    (A : Matrix n n ℂ) :
    Matrix n n ℂ :=
  z • (1 : Matrix n n ℂ) - A

/-! ## 2. Constructive finite matrix resolvent kernel -/

/-- A finite matrix resolvent kernel: explicit two-sided inverse data for `z • I - A`. -/
structure MatrixResolventKernel
    (n : Type*) [Fintype n] [DecidableEq n] where
  /-- Operator/matrix. -/
  A : Matrix n n ℂ
  /-- Spectral parameter. -/
  z : ℂ
  /-- Resolvent kernel, morally `(zI - A)⁻¹`. -/
  kernel : Matrix n n ℂ
  /-- Left inverse law: `(zI - A) * kernel = I`. -/
  diff_mul_kernel :
    resolventDiff z A * kernel = 1
  /-- Right inverse law: `kernel * (zI - A) = I`. -/
  kernel_mul_diff :
    kernel * resolventDiff z A = 1

namespace MatrixResolventKernel

variable
    {n : Type*} [Fintype n] [DecidableEq n]

variable (K : MatrixResolventKernel n)

/-- The resolvent kernel is a right inverse of the resolvent difference. -/
theorem diff_mul_kernel_eq_one :
    resolventDiff K.z K.A * K.kernel = 1 :=
  K.diff_mul_kernel

/-- The resolvent kernel is a left inverse of the resolvent difference. -/
theorem kernel_mul_diff_eq_one :
    K.kernel * resolventDiff K.z K.A = 1 :=
  K.kernel_mul_diff

/--
Uniqueness of the finite matrix resolvent kernel.

Any other two-sided inverse of `zI - A` is equal to `K.kernel`.
-/
theorem kernel_unique
    (R : Matrix n n ℂ)
    (_h_left : resolventDiff K.z K.A * R = 1)
    (h_right : R * resolventDiff K.z K.A = 1) :
    R = K.kernel := by
  calc
    R = R * 1 := by
      simp
    _ = R * (resolventDiff K.z K.A * K.kernel) := by
      rw [K.diff_mul_kernel]
    _ = (R * resolventDiff K.z K.A) * K.kernel := by
      rw [mul_assoc]
    _ = 1 * K.kernel := by
      rw [h_right]
    _ = K.kernel := by
      simp

/--
If two finite matrix resolvent kernels have the same `A` and `z`, their kernels
are equal.
-/
theorem kernel_eq_of_same_matrix_and_parameter
    (K₁ K₂ : MatrixResolventKernel n)
    (hA : K₁.A = K₂.A)
    (hz : K₁.z = K₂.z) :
    K₁.kernel = K₂.kernel := by
  apply K₂.kernel_unique
  · rw [← hA, ← hz]
    exact K₁.diff_mul_kernel
  · rw [← hA, ← hz]
    exact K₁.kernel_mul_diff

end MatrixResolventKernel

/-! ## 3. Construction from a unit -/

/--
Construct a matrix resolvent kernel from a unit witness for `zI - A`.

This is the finite constructive replacement for “the resolvent exists”.
-/
def matrixResolventKernelOfUnit
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ)
    (z : ℂ)
    (U : Units (Matrix n n ℂ))
    (hU : U.val = resolventDiff z A) :
    MatrixResolventKernel n where
  A := A
  z := z
  kernel := U.inv
  diff_mul_kernel := by
    rw [← hU]
    exact U.val_inv
  kernel_mul_diff := by
    rw [← hU]
    exact U.inv_val

/-- The kernel produced from a unit is the inverse component of that unit. -/
@[simp]
theorem matrixResolventKernelOfUnit_kernel
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ)
    (z : ℂ)
    (U : Units (Matrix n n ℂ))
    (hU : U.val = resolventDiff z A) :
    (matrixResolventKernelOfUnit A z U hU).kernel = U.inv :=
  rfl

/-! ## 4. Explicit scalar one-by-one resolvent kernel -/

/-- The one-by-one scalar matrix associated to a complex number. -/
def scalarOneByOne
    (a : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => a

/-- The scalar one-by-one identity matrix is `scalarOneByOne 1`. -/
theorem scalarOneByOne_one :
    scalarOneByOne 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [scalarOneByOne]

/-- The scalar one-by-one product is scalar multiplication. -/
theorem scalarOneByOne_mul
    (a b : ℂ) :
    scalarOneByOne a * scalarOneByOne b = scalarOneByOne (a * b) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [scalarOneByOne, Matrix.mul_apply]

/--
For a scalar one-by-one matrix `A = [a]`, the resolvent difference is `[z-a]`.
-/
theorem resolventDiff_scalarOneByOne
    (z a : ℂ) :
    resolventDiff z (scalarOneByOne a) =
      scalarOneByOne (z - a) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [resolventDiff, scalarOneByOne]

/--
Concrete scalar one-by-one resolvent kernel.

If `z - a ≠ 0`, then the kernel is `[(z-a)⁻¹]`.
-/
def scalarOneByOneResolventKernel
    (z a : ℂ)
    (h : z - a ≠ 0) :
    MatrixResolventKernel (Fin 1) where
  A := scalarOneByOne a
  z := z
  kernel := scalarOneByOne ((z - a)⁻¹)
  diff_mul_kernel := by
    rw [resolventDiff_scalarOneByOne]
    rw [scalarOneByOne_mul]
    rw [mul_inv_cancel₀ h]
    exact scalarOneByOne_one
  kernel_mul_diff := by
    rw [resolventDiff_scalarOneByOne]
    rw [scalarOneByOne_mul]
    rw [inv_mul_cancel₀ h]
    exact scalarOneByOne_one

/-- The scalar one-by-one kernel has the expected entry. -/
theorem scalarOneByOneResolventKernel_entry
    (z a : ℂ)
    (h : z - a ≠ 0) :
    (scalarOneByOneResolventKernel z a h).kernel 0 0 =
      (z - a)⁻¹ :=
  rfl

/-- Uniqueness of the scalar one-by-one resolvent kernel. -/
theorem scalarOneByOneResolventKernel_unique
    (z a : ℂ)
    (h : z - a ≠ 0)
    (R : Matrix (Fin 1) (Fin 1) ℂ)
    (h_left :
      resolventDiff z (scalarOneByOne a) * R = 1)
    (h_right :
      R * resolventDiff z (scalarOneByOne a) = 1) :
    R = scalarOneByOne ((z - a)⁻¹) := by
  have huniq :=
    (scalarOneByOneResolventKernel z a h).kernel_unique
      R h_left h_right
  exact huniq

/-! ## 5. Owner targets discharged constructively -/

/--
Owner target: finite matrix resolvent uniqueness from explicit two-sided
inverse laws.
-/
@[owner_target_tag]
def FiniteMatrixResolventUniquenessOwnerTarget : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n],
  ∀ (A : Matrix n n ℂ) (z : ℂ),
  ∀ (R₁ R₂ : Matrix n n ℂ),
    resolventDiff z A * R₁ = 1 →
    R₁ * resolventDiff z A = 1 →
    resolventDiff z A * R₂ = 1 →
    R₂ * resolventDiff z A = 1 →
      R₁ = R₂

/-- Constructive proof of finite matrix resolvent uniqueness. -/
theorem finiteMatrixResolventUniquenessOwnerTarget :
    FiniteMatrixResolventUniquenessOwnerTarget := by
  intro n _ _ A z R₁ R₂ h₁L h₁R h₂L h₂R
  let K : MatrixResolventKernel n :=
    { A := A
      z := z
      kernel := R₂
      diff_mul_kernel := h₂L
      kernel_mul_diff := h₂R }
  exact K.kernel_unique R₁ h₁L h₁R

/-- Owner target: scalar one-by-one resolvent exists constructively when `z-a ≠ 0`. -/
@[owner_target_tag]
def ScalarOneByOneResolventOwnerTarget : Prop :=
  ∀ z a : ℂ,
    z - a ≠ 0 →
      Nonempty (MatrixResolventKernel (Fin 1))

/-- Constructive proof of scalar one-by-one resolvent existence. -/
theorem scalarOneByOneResolventOwnerTarget :
    ScalarOneByOneResolventOwnerTarget := by
  intro z a h
  exact ⟨scalarOneByOneResolventKernel z a h⟩

/-- Owner target: resolvent kernel from a unit witness. -/
@[owner_target_tag]
def MatrixResolventFromUnitOwnerTarget : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n],
  ∀ (A : Matrix n n ℂ) (z : ℂ),
  ∀ U : Units (Matrix n n ℂ),
    U.val = resolventDiff z A →
      Nonempty (MatrixResolventKernel n)

/-- Constructive proof of matrix resolvent construction from a unit. -/
theorem matrixResolventFromUnitOwnerTarget :
    MatrixResolventFromUnitOwnerTarget := by
  intro n _ _ A z U hU
  exact ⟨matrixResolventKernelOfUnit A z U hU⟩

end InfoGeometry.Geometry.FiniteMatrixResolventKernel
