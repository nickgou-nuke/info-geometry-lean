/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases

/-!
# A shared noncommuting pair in the full matrix algebra

Both matrices have off-diagonal entries. Their products differ over every
nontrivial coefficient ring, including characteristic two. They supply the
actual coefficient pair used by the bounded-operator BKM example and the
nested BdG curvature example.
-/

namespace InfoGeometry.Algebra.MatrixNoncommutativity

variable {A : Type*} [Ring A]

def swapMatrix : Matrix (Fin 2) (Fin 2) A := !![0, 1; 1, 0]

def tiltedMatrix : Matrix (Fin 2) (Fin 2) A := !![1, 1; 1, 0]

/-- The two full matrices do not commute over any nontrivial ring. -/
theorem swapMatrix_mul_tiltedMatrix_ne [Nontrivial A] :
    (swapMatrix : Matrix (Fin 2) (Fin 2) A) * tiltedMatrix ≠
      tiltedMatrix * swapMatrix := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1) h
  simpa [swapMatrix, tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two] using hentry

variable [StarRing A]

@[simp] theorem star_swapMatrix : star (swapMatrix (A := A)) = swapMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMatrix]

@[simp] theorem star_tiltedMatrix : star (tiltedMatrix (A := A)) = tiltedMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tiltedMatrix]

end InfoGeometry.Algebra.MatrixNoncommutativity
