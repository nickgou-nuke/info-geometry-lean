import Mathlib

open Matrix

/-!
# Affine A1^(1) Imaginary Root

This module records the concrete Cartan matrix for affine type A1^(1) and
checks the primitive imaginary root directly.  The theorem statements are
explicit matrix identities over `Z`, not prose-only claims.
-/

/-- The affine A1^(1) generalized Cartan matrix. -/
def A1_1Cartan : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -2;
     -2, 2]

/-- The primitive positive imaginary root delta = alpha_0 + alpha_1. -/
def imaginaryRootDelta : Matrix (Fin 2) (Fin 1) ℤ :=
  !![1; 1]

theorem det_A1_1Cartan_eq_zero : A1_1Cartan.det = 0 := by
  simp [A1_1Cartan, Matrix.det_fin_two]

theorem A1_1Cartan_mul_delta_eq_zero :
    A1_1Cartan * imaginaryRootDelta = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A1_1Cartan, imaginaryRootDelta, Matrix.mul_apply]

theorem A1_1Cartan_symmetric : A1_1Cartanᵀ = A1_1Cartan := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A1_1Cartan]

theorem delta_first_coord_eq_one : imaginaryRootDelta 0 0 = 1 := by
  norm_num [imaginaryRootDelta]

theorem delta_second_coord_eq_one : imaginaryRootDelta 1 0 = 1 := by
  norm_num [imaginaryRootDelta]

theorem imaginaryRootDelta_ne_zero : imaginaryRootDelta ≠ 0 := by
  intro h
  have h00 : imaginaryRootDelta 0 0 = (0 : ℤ) := by
    rw [h]
    rfl
  norm_num [imaginaryRootDelta] at h00

/--
The null root is primitive: its two simple-root coefficients have greatest
common divisor one.
-/
theorem imaginaryRootDelta_primitive :
    Int.gcd (imaginaryRootDelta 0 0) (imaginaryRootDelta 1 0) = 1 := by
  norm_num [imaginaryRootDelta]

/--
Main non-vacuous package for the affine A1^(1) imaginary root: the Cartan
matrix is singular, symmetric, and kills the nonzero primitive vector delta.
-/
theorem affine_A1_1_imaginary_root_theorem :
    A1_1Cartan.det = 0 ∧
    A1_1Cartanᵀ = A1_1Cartan ∧
    A1_1Cartan * imaginaryRootDelta = 0 ∧
    imaginaryRootDelta ≠ 0 ∧
    Int.gcd (imaginaryRootDelta 0 0) (imaginaryRootDelta 1 0) = 1 := by
  exact ⟨det_A1_1Cartan_eq_zero,
    A1_1Cartan_symmetric,
    A1_1Cartan_mul_delta_eq_zero,
    imaginaryRootDelta_ne_zero,
    imaginaryRootDelta_primitive⟩
