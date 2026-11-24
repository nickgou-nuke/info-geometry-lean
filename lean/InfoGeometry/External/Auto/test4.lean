/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

namespace Test4

abbrev Q := ℚ

def zeroMatrixA : Matrix (Fin 3) (Fin 3) Q := 0
def zeroMatrixB : Matrix (Fin 3) (Fin 3) Q := 0

def zeroCommutatorDeterminant : Q :=
  det (⁅zeroMatrixA, zeroMatrixB⁆)

lemma zeroCommutator_det_trace_cube_identity :
    zeroCommutatorDeterminant = (1 / 3 : Q) * trace (⁅zeroMatrixA, zeroMatrixB⁆ ^ 3) := by
  change det ((0 : Matrix (Fin 3) (Fin 3) Q) * 0 - 0 * 0) =
    (1 / 3 : Q) * trace (((0 : Matrix (Fin 3) (Fin 3) Q) * 0 - 0 * 0) ^ 3)
  have hz : (0 : Matrix (Fin 3) (Fin 3) Q) * 0 - 0 * 0 = 0 := by
    simp
  rw [hz, Matrix.det_zero]
  simp


def diagonalA : Matrix (Fin 3) (Fin 3) Q := !![1, 0, 0; 0, 0, 0; 0, 0, -1]

def cyclicShiftB : Matrix (Fin 3) (Fin 3) Q := !![0, 1, 0; 0, 0, 1; 1, 0, 0]


theorem diagonalA_cyclicShiftB_noncommute :
    diagonalA * cyclicShiftB ≠ cyclicShiftB * diagonalA := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) Q => M 0 1) h
  norm_num [diagonalA, cyclicShiftB, Matrix.mul_apply, Fin.sum_univ_succ] at h01


def concreteBracket : Matrix (Fin 3) (Fin 3) Q := diagonalA * cyclicShiftB - cyclicShiftB * diagonalA

/-- A concrete nonzero concreteBracket has determinant `-2` and cubic trace `-6`. -/
theorem concreteBracket_det_and_trace_cube :
    concreteBracket.det = -2 ∧ Matrix.trace (concreteBracket ^ 3) = -6 ∧
      concreteBracket.det = (1 / 3 : Q) * Matrix.trace (concreteBracket ^ 3) := by
  norm_num [concreteBracket, diagonalA, cyclicShiftB, Matrix.det_fin_three,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

end Test4
