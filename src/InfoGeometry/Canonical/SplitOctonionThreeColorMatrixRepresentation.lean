import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The rational matrix-unit atom

This file records the concrete `M₂(ℚ)` matrix-unit calculus used by one
colour of the split-quaternion picture.  It is deliberately independent of
the non-associative split-octonion carrier: an identification with a
particular octonion core requires a separate linear and multiplicative
bridge.
-/

namespace InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℚ

def nPlus : M₂ := !![1, 0; 0, 0]

def nMinus : M₂ := !![0, 0; 0, 1]

def sigmaPlus : M₂ := !![0, 1; 0, 0]

def sigmaMinus : M₂ := !![0, 0; 1, 0]

@[simp] theorem nPlus_add_nMinus : nPlus + nMinus = (1 : M₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nPlus, nMinus]

@[simp] theorem sigmaPlus_mul_sigmaMinus :
    sigmaPlus * sigmaMinus = nPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, nPlus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem sigmaMinus_mul_sigmaPlus :
    sigmaMinus * sigmaPlus = nMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, nMinus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem sigmaMinus_mul_nMinus : sigmaMinus * nMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaMinus, nMinus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem sigmaPlus_sq : sigmaPlus * sigmaPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem sigmaMinus_sq : sigmaMinus * sigmaMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaMinus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem sigmaPlus_mul_nMinus : sigmaPlus * nMinus = sigmaPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, nMinus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem nPlus_mul_nMinus : nPlus * nMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nPlus, nMinus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem nMinus_mul_nPlus : nMinus * nPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nPlus, nMinus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem nPlus_sq : nPlus * nPlus = nPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nPlus, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem nMinus_sq : nMinus * nMinus = nMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nMinus, Matrix.mul_apply, Fin.sum_univ_succ]

end InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation
