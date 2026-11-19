/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Chiral basis change matrix

The rational change of coordinates between the chiral Peirce--Witt basis
`(n₊, σᵢ₊, σⱼ₊, σₖ₊, n₋, σᵢ₋, σⱼ₋, σₖ₋)` and the native split-octonion
basis `(1, ℓ, i, iℓ, j, jℓ, k, kℓ)`.

This file stores the explicit forward and inverse matrices and certifies that
they are mutual inverses.
-/

def chiralToStandard : Matrix (Fin 8) (Fin 8) ℚ :=
  !![
    1 / 2,  0,      0,     0,     1 / 2,  0,     0,     0;
    1 / 2,  0,      0,     0,    -1 / 2,  0,     0,     0;
    0,     -1 / 2,  0,     0,     0,     1 / 2,  0,     0;
    0,      1 / 2,  0,     0,     0,     1 / 2,  0,     0;
    0,      0,     -1 / 2,  0,     0,     0,     1 / 2,  0;
    0,      0,      1 / 2,  0,     0,     0,     1 / 2,  0;
    0,      0,      0,    -1 / 2,  0,     0,     0,     1 / 2;
    0,      0,      0,     1 / 2,  0,     0,     0,     1 / 2
  ]

def standardToChiral : Matrix (Fin 8) (Fin 8) ℚ :=
  !![
    1,  1,  0,  0,  0,  0,  0,  0;
    0,  0, -1,  1,  0,  0,  0,  0;
    0,  0,  0,  0, -1,  1,  0,  0;
    0,  0,  0,  0,  0,  0, -1,  1;
    1, -1,  0,  0,  0,  0,  0,  0;
    0,  0,  1,  1,  0,  0,  0,  0;
    0,  0,  0,  0,  1,  1,  0,  0;
    0,  0,  0,  0,  0,  0,  1,  1
  ]

/-- Matrix units in opposite off-diagonal positions in the actual coefficient
matrix carrier. -/
def matrixUnit01 : Matrix (Fin 8) (Fin 8) ℚ :=
  Matrix.single 0 1 1

def matrixUnit10 : Matrix (Fin 8) (Fin 8) ℚ :=
  Matrix.single 1 0 1

/-- The matrix operator carrier is genuinely noncommutative. -/
theorem matrix_units_noncommute :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℚ => M 0 0) h
  norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Matrix.single] at h00

theorem chiralToStandard_mul_standardToChiral :
    chiralToStandard * standardToChiral = (1 : Matrix (Fin 8) (Fin 8) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralToStandard, standardToChiral, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem standardToChiral_mul_chiralToStandard :
    standardToChiral * chiralToStandard = (1 : Matrix (Fin 8) (Fin 8) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralToStandard, standardToChiral, Matrix.mul_apply,
      Fin.sum_univ_succ]

end InfoGeometry.Canonical
