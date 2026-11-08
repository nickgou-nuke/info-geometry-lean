/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Finite Matrix Symmetric–Skew and Off-Diagonal Identities

This file formalizes finite `2 × 2` matrix identities using Mathlib's native
`Matrix (Fin 2) (Fin 2) R` carrier: the symmetric/skew Frobenius decomposition,
a restricted off-diagonal square/determinant identity, and finite examples.

The historical filename and the chat's QGT/Berry/ER=EPR interpretation are not
authority. These theorems do not construct a quantum geometric tensor, Fisher
metric, Berry curvature, entanglement wedge, or ER=EPR correspondence.
The separate cross-pairing formula is treated by the finite Metriplectic owner.
The chat's claimed `C_EPR = 2 * A_ER` identity is not proved by these matrix
identities; any ER=EPR interpretation requires its own explicit carrier and
proved bridge.
-/
open scoped Matrix

namespace InfoGeometry.QuantumContext.FiniteMatrixSymmetricSkew

variable {R : Type*} [CommRing R]

/-- Native `2 × 2` matrix carrier over `R`. -/
abbrev Mat2 (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- Frobenius pairing on matrices, defined by `Tr(Aᵀ B)`. -/
def frobeniusPairing (A B : Mat2 R) : R :=
  Matrix.trace (Matrix.transpose A * B)

/-- Doubled symmetric part `A + Aᵀ`. -/
def symmetricPartTwice (A : Mat2 R) : Mat2 R :=
  A + Matrix.transpose A

/-- Doubled skew-symmetric part `A - Aᵀ`. -/
def skewPartTwice (A : Mat2 R) : Mat2 R :=
  A - Matrix.transpose A

/-- Transposing the symmetric part leaves it unchanged. -/
theorem symmetricPartTwice_is_symmetric (A : Mat2 R) :
    Matrix.transpose (symmetricPartTwice A) = symmetricPartTwice A := by
  simp [symmetricPartTwice, add_comm]

/-- The doubled symmetric and skew parts reconstruct `2 • A`. -/
theorem symmetric_add_skew_eq_two_smul (A : Mat2 R) :
    symmetricPartTwice A + skewPartTwice A = 2 • A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricPartTwice, skewPartTwice, Matrix.transpose_apply]
  <;> ring

/-- Symmetric and skew-symmetric parts are orthogonal in the Frobenius pairing. -/
theorem symmetric_skew_frobenius_pairing_zero (A : Mat2 R) :
    frobeniusPairing (symmetricPartTwice A) (skewPartTwice A) = 0 := by
  simp [frobeniusPairing, symmetricPartTwice, skewPartTwice,
    Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  ring_nf

/-- Pythagorean partition of the Frobenius norm for the doubled parts. -/
theorem symmetric_skew_pythagorean_frobenius_norm (A : Mat2 R) :
    frobeniusPairing (symmetricPartTwice A) (symmetricPartTwice A) +
        frobeniusPairing (skewPartTwice A) (skewPartTwice A) =
      4 * frobeniusPairing A A := by
  simp [frobeniusPairing, symmetricPartTwice, skewPartTwice,
    Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  ring_nf

/-- Off-diagonal `2 × 2` matrix used in the finite square/determinant identity. -/
def offDiagonalMatrix (γL γR : R) : Mat2 R :=
  !![(0 : R), γL; γR, 0]

/-- The square of the off-diagonal matrix is a scalar diagonal matrix. -/
theorem offDiagonalMatrix_sq_diagonal (γL γR : R) :
    offDiagonalMatrix γL γR * offDiagonalMatrix γL γR =
      !![γL * γR, (0 : R); 0, γL * γR] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- Negative determinant of the off-diagonal matrix. -/
def negativeDeterminant (γL γR : R) : R :=
  -Matrix.det (offDiagonalMatrix γL γR)

/-- Trace of the square of the off-diagonal matrix. -/
def twiceOffDiagonalProduct (γL γR : R) : R :=
  Matrix.trace (offDiagonalMatrix γL γR * offDiagonalMatrix γL γR)

/-- The trace of the square equals twice both the negative determinant and
`γL * γR`. -/
theorem offDiagonalDeterminant_identity (γL γR : R) :
    twiceOffDiagonalProduct γL γR = 2 * negativeDeterminant γL γR ∧
      twiceOffDiagonalProduct γL γR = 2 * (γL * γR) := by
  constructor
  · dsimp [twiceOffDiagonalProduct, negativeDeterminant, offDiagonalMatrix]
    simp [Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]
    ring_nf
  · dsimp [twiceOffDiagonalProduct, offDiagonalMatrix]
    simp [Matrix.trace, Fin.sum_univ_two]
    ring_nf

/-- If the upper off-diagonal entry vanishes, the matrix squares to zero and
its negative determinant is zero. -/
theorem offDiagonalMatrix_nilpotent_left_zero (γR : R) :
    (offDiagonalMatrix 0 γR) 1 0 = γR ∧
      offDiagonalMatrix 0 γR * offDiagonalMatrix 0 γR = 0 ∧
      negativeDeterminant 0 γR = 0 := by
  refine ⟨by simp [offDiagonalMatrix], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [offDiagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [negativeDeterminant, offDiagonalMatrix, Matrix.det_fin_two]

end InfoGeometry.QuantumContext.FiniteMatrixSymmetricSkew
