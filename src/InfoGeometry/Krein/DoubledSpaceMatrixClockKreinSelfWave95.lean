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

/-- The represented elliptic clock generator is Krein-self-adjoint. -/
theorem ρclock_matrixClockAxis_kreinSelfAdjoint :
    KreinSpace.kreinAdjoint (H := DoubledSpace E)
        (ρclock (E := E) matrixClockAxis) =
      ρclock (E := E) matrixClockAxis := by
  rw [ρclock_kreinAdjoint]
  have htrans : matrixClockAxis.transpose = -matrixClockAxis := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixClockAxis, Matrix.transpose_apply]
  rw [htrans]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixClockAxis, matrixEpsilon, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixClockAxis_kreinSelfAdjoint
