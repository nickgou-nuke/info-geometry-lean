import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal

/-!
# Upper-triangular QR readout

This file does not construct Gram--Schmidt.  It records the finite property
readout that an already upper-triangular matrix has the QR factorization
`A = I * A`, with orthogonal factor `I` and triangular factor `A`.
-/

open Matrix
open scoped Matrix

namespace InfoGeometry.Spectral.Numerical

/-- Check if a matrix is upper triangular -/
def isUpperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, i.val > j.val → A i j = 0

/-- The identity matrix with explicit type -/
def identityMatrix {n : ℕ} : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then (1 : ℝ) else 0

@[simp] theorem identityMatrix_eq_one {n : ℕ} :
    (identityMatrix : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j
  simp [identityMatrix, Matrix.one_apply]

/-- Check if a matrix is orthogonal -/
def isOrthogonal {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Q.transpose * Q = identityMatrix

/-- Upper-triangular QR readout `A = I * A`. -/
def qrDecomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (identityMatrix, A)

/- Extract Q factor -/
def qrQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (qrDecomposition A).1

/- Extract R factor -/
def qrR {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (qrDecomposition A).2

/- QR frame for Serre SS page -/
def serrePageFrame {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  qrQ A

/-- Correctness of the upper-triangular readout `A = I * A`. -/
theorem qrDecomposition_correct {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : isUpperTriangular A) :
    let QR := qrDecomposition A
    A = QR.1 * QR.2 ∧ isOrthogonal QR.1 ∧ isUpperTriangular QR.2 := by
  simp [qrDecomposition, isOrthogonal, hA]

end InfoGeometry.Spectral.Numerical
