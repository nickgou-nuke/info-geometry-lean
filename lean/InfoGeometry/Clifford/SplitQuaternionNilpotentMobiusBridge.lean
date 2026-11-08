import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitQuaternionNilpotentFlow

namespace InfoGeometry.Clifford.SplitQuaternionNilpotentMobiusBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.SplitQuaternionNilpotentFlow

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

def lowerParabolicMatrix (T : ℝ) : M2R :=
  !![(1 : ℝ), 0; -2 * T, 1]

def upperParabolicMatrix (T : ℝ) : M2R :=
  !![(1 : ℝ), -2 * T; 0, 1]

def sheetFlip : M2R := !![(0 : ℝ), 1; 1, 0]

def toComplex (A : M2R) : M2C := fun i j => A i j

noncomputable def mobiusAction (A : M2C) (z : ℂ) : ℂ :=
  (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)

theorem nilpotent_exp_toMatrix (T : ℝ) :
    toMatrix (sq_nilpotent_exp T) = lowerParabolicMatrix T := by
  rw [sq_nilpotent_exp_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, lowerParabolicMatrix] <;> ring

theorem lowerParabolicMatrix_det (T : ℝ) :
    (lowerParabolicMatrix T).det = 1 := by
  simp [lowerParabolicMatrix, Matrix.det_fin_two]

theorem lowerParabolicMatrix_trace (T : ℝ) :
    Matrix.trace (lowerParabolicMatrix T) = 2 := by
  simp [lowerParabolicMatrix, Matrix.trace, Fin.sum_univ_two]
  norm_num

theorem lowerParabolicMatrix_trace_sq (T : ℝ) :
    (Matrix.trace (lowerParabolicMatrix T)) ^ 2 = 4 := by
  rw [lowerParabolicMatrix_trace]
  norm_num

theorem sheetFlip_sq : sheetFlip * sheetFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetFlip_conjugates_lower (T : ℝ) :
    sheetFlip * lowerParabolicMatrix T * sheetFlip =
      upperParabolicMatrix T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, lowerParabolicMatrix, upperParabolicMatrix,
      Matrix.mul_apply,
      Fin.sum_univ_two]

theorem lowerParabolicMatrix_ne_one {T : ℝ} (hT : T ≠ 0) :
    lowerParabolicMatrix T ≠ (1 : M2R) := by
  intro h
  have hentry := congrArg (fun A : M2R => A 1 0) h
  have hzero : (-2 : ℝ) * T = 0 := by
    simpa [lowerParabolicMatrix] using hentry
  apply hT
  linarith

theorem lowerParabolicMatrix_ne_neg_one {T : ℝ} :
    lowerParabolicMatrix T ≠ -(1 : M2R) := by
  intro h
  have hentry := congrArg (fun A : M2R => A 0 0) h
  norm_num [lowerParabolicMatrix] at hentry

noncomputable def lowerParabolicSL2 (T : ℝ) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨lowerParabolicMatrix T, lowerParabolicMatrix_det T⟩

theorem lowerParabolic_mobius_action (T : ℝ) (z : ℂ) :
    mobiusAction (toComplex (lowerParabolicMatrix T)) z =
      z / ((1 : ℂ) - 2 * (T : ℂ) * z) := by
  simp [mobiusAction, toComplex, lowerParabolicMatrix]
  congr 2
  ring

theorem upperParabolic_mobius_action (T : ℝ) (z : ℂ) :
    mobiusAction (toComplex (upperParabolicMatrix T)) z =
      z - 2 * (T : ℂ) := by
  simp [mobiusAction, toComplex, upperParabolicMatrix]
  ring

end InfoGeometry.Clifford.SplitQuaternionNilpotentMobiusBridge
