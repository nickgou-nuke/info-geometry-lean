import Mathlib

/-!
# Finite biquaternion dual-root regularizer

This module extracts the theorem-safe finite core from the proposed
non-Hermitian Pauli/BdG/MoE regularizer story.

Closed content:

* every `2 × 2` complex matrix splits into scalar trace and traceless parts;
* the traceless part has trace zero;
* a traceless Pauli-vector matrix squares to a scalar matrix;
* explicit finite roots of `+I` and `-I` are checked by multiplication;
* the two centered boundary charts `T - I` and `T + I` can carry explicit
  square-zero, determinant-zero nilpotent boundaries.

No analytic matrix logarithm, entropy minimization, exceptional-point topology,
continuum holonomy, QCD/GR claim, or physical BdG theorem is asserted here.
-/

noncomputable section

namespace BiquaternionDualRootRegularizer

open Matrix
open scoped Matrix

/-- Native `2 × 2` complex matrix carrier for the finite biquaternion shadow. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The `2 × 2` identity matrix. -/
def I2 : Mat2C := 1

/-- The `2 × 2` zero matrix. -/
def Z2 : Mat2C := 0

/-- Explicit two-by-two trace. -/
def tr2 (A : Mat2C) : ℂ := A 0 0 + A 1 1

/-- Scalar matrix `c I`. -/
def scalarCenter (c : ℂ) : Mat2C := !![c, 0; 0, c]

/-- Trace scalar component `(tr A / 2) I`. -/
def traceScalarPart (A : Mat2C) : Mat2C := scalarCenter (tr2 A / 2)

/-- Traceless anisotropic component of a finite biquaternion matrix. -/
def tracelessPart (A : Mat2C) : Mat2C := A - traceScalarPart A

/-- Trace splitting is exact: scalar plus traceless reconstructs the matrix. -/
theorem traceScalarPart_add_tracelessPart (A : Mat2C) :
    traceScalarPart A + tracelessPart A = A := by
  ext i j
  simp [tracelessPart]

/-- The anisotropic component has zero trace. -/
theorem tr2_tracelessPart_zero (A : Mat2C) : tr2 (tracelessPart A) = 0 := by
  simp [tr2, tracelessPart, traceScalarPart, scalarCenter]
  ring

/-- A generic traceless Pauli-vector matrix. -/
def pauliVector (x y z : ℂ) : Mat2C := !![x, y; z, -x]

/-- Pauli-vector matrices are traceless. -/
theorem tr2_pauliVector (x y z : ℂ) : tr2 (pauliVector x y z) = 0 := by
  simp [tr2, pauliVector]

/-- Finite self-closure: a traceless Pauli-vector square is scalar. -/
theorem pauliVector_sq_scalar (x y z : ℂ) :
    pauliVector x y z * pauliVector x y z = scalarCenter (x ^ 2 + y * z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, scalarCenter, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- First explicit root of `+I`. -/
def sigmaX : Mat2C := !![0, 1; 1, 0]

/-- Second explicit root of `+I`. -/
def sigmaZ : Mat2C := !![1, 0; 0, -1]

/-- Explicit root of `-I`, the real skew Pauli atom. -/
def skewJ : Mat2C := !![0, -1; 1, 0]

/-- `sigmaX` squares to `+I`. -/
theorem sigmaX_sq : sigmaX * sigmaX = I2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, I2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `sigmaZ` squares to `+I`. -/
theorem sigmaZ_sq : sigmaZ * sigmaZ = I2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, I2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `skewJ` squares to `-I`. -/
theorem skewJ_sq : skewJ * skewJ = -I2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewJ, I2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The square-zero nilpotent boundary atom. -/
def N : Mat2C := !![0, 1; 0, 0]

/-- Explicit determinant for `2 × 2` matrices. -/
def det2 (A : Mat2C) : ℂ := A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- The boundary atom is square-zero. -/
theorem N_sq : N * N = Z2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Z2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The boundary atom has determinant zero. -/
theorem det2_N : det2 N = 0 := by
  simp [det2, N]

/-- The boundary atom is traceless. -/
theorem tr2_N : tr2 N = 0 := by
  simp [tr2, N]

/-- `T = I + N` lies on the `I`-centered nilpotent boundary. -/
def plusBoundary : Mat2C := I2 + N

/-- `T = -I + N` lies on the `-I`-centered nilpotent boundary. -/
def minusBoundary : Mat2C := -I2 + N

/-- The `I`-centered residual of `plusBoundary` is square-zero. -/
theorem plusBoundary_sub_I_sq : (plusBoundary - I2) * (plusBoundary - I2) = Z2 := by
  simp [plusBoundary, N_sq]

/-- The `I`-centered residual of `plusBoundary` has determinant zero. -/
theorem det2_plusBoundary_sub_I : det2 (plusBoundary - I2) = 0 := by
  simp [plusBoundary, det2_N]

/-- The `-I`-centered residual of `minusBoundary` is square-zero. -/
theorem minusBoundary_add_I_sq : (minusBoundary + I2) * (minusBoundary + I2) = Z2 := by
  simp [minusBoundary, N_sq]

/-- The `-I`-centered residual of `minusBoundary` has determinant zero. -/
theorem det2_minusBoundary_add_I : det2 (minusBoundary + I2) = 0 := by
  simp [minusBoundary, det2_N]

/-- Consolidated finite dual-root regularizer packet. -/
theorem finite_dual_root_regularizer_packet :
    (∀ A : Mat2C, traceScalarPart A + tracelessPart A = A) ∧
      (∀ A : Mat2C, tr2 (tracelessPart A) = 0) ∧
      (∀ x y z : ℂ,
        pauliVector x y z * pauliVector x y z = scalarCenter (x ^ 2 + y * z)) ∧
      sigmaX * sigmaX = I2 ∧
      sigmaZ * sigmaZ = I2 ∧
      skewJ * skewJ = -I2 ∧
      (plusBoundary - I2) * (plusBoundary - I2) = Z2 ∧
      det2 (plusBoundary - I2) = 0 ∧
      (minusBoundary + I2) * (minusBoundary + I2) = Z2 ∧
      det2 (minusBoundary + I2) = 0 := by
  exact ⟨traceScalarPart_add_tracelessPart, tr2_tracelessPart_zero,
    pauliVector_sq_scalar, sigmaX_sq, sigmaZ_sq, skewJ_sq,
    plusBoundary_sub_I_sq, det2_plusBoundary_sub_I,
    minusBoundary_add_I_sq, det2_minusBoundary_add_I⟩

end BiquaternionDualRootRegularizer

end noncomputable section
