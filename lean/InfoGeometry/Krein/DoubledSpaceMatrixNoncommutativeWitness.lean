/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

/-- The represented matrix generators have a genuine noncommutative product. -/
theorem matrixJ_matrixEpsilon_ne_commute :
    matrixJ * matrixEpsilon ≠ matrixEpsilon * matrixJ := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [matrixJ, matrixEpsilon, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- Their commutator is nonzero in the real two-by-two matrix carrier. -/
theorem matrixJ_matrixEpsilon_commutator_ne_zero :
    matrixJ * matrixEpsilon - matrixEpsilon * matrixJ ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [matrixJ, matrixEpsilon, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- Typed existential witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem mat2R_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨matrixJ, matrixEpsilon, matrixJ_matrixEpsilon_ne_commute⟩

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixJ_matrixEpsilon_ne_commute
#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixJ_matrixEpsilon_commutator_ne_zero
