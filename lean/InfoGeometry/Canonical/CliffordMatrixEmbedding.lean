/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Block diagonal matrix carrier

This owner records the actual block diagonal matrix construction. A matrix
endomorphism of the vector carrier is not, by itself, a Clifford algebra
element: the former acts on vectors, while the Clifford algebra is generated
by vectors subject to the quadratic relation. No arbitrary matrix-to-Clifford
embedding is asserted here.
-/

namespace InfoGeometry.Canonical

variable {R : Type*} [Zero R]
variable {m n : Type*} [DecidableEq n]

/-- The block diagonal matrix associated to a family of square blocks. The
outer index selects a block and the inner index selects a row or column. -/
def blockDiagonalMatrix (A : n → Matrix m m R) :
    Matrix (n × m) (n × m) R :=
  fun i j => if i.1 = j.1 then A i.1 i.2 j.2 else 0

@[simp]
theorem blockDiagonalMatrix_sameBlock (A : n → Matrix m m R)
    (k : n) (i j : m) :
    blockDiagonalMatrix A (k, i) (k, j) = A k i j := by
  simp [blockDiagonalMatrix]

@[simp]
theorem blockDiagonalMatrix_differentBlocks (A : n → Matrix m m R)
    (k l : n) (i j : m) (h : k ≠ l) :
    blockDiagonalMatrix A (k, i) (l, j) = 0 := by
  simp [blockDiagonalMatrix, h]

end InfoGeometry.Canonical
