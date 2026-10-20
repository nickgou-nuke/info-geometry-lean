/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixKreinAdjointWave94

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The matrix realization of the modular sheet swap is Krein-skew-adjoint.

This is the matrix-side transport of the native modular swap's
Krein-skew-adjointness, with the diagonal matrix `matrixEpsilon` supplying the
fundamental symmetry in the representation formula.
-/
theorem ρclock_matrixJ_kreinSkewAdjoint :
    KreinSpace.kreinAdjoint (H := DoubledSpace E)
        (ρclock (E := E) matrixJ) =
      -(ρclock (E := E) matrixJ) := by
  rw [ρclock_kreinAdjoint]
  have htrans : matrixJ.transpose = matrixJ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixJ, Matrix.transpose_apply]
  rw [htrans]
  rw [← (ρclock (E := E)).map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixJ, matrixEpsilon, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixJ_kreinSkewAdjoint
