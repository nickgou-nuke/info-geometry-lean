/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Krein.DoubledSpaceMatrixClockFaithfulWave92
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- The faithful doubled-space representation transports the canonical
noncommutativity of the real matrix units to represented operators. -/
theorem ρclock_matrix_units_noncommute
    [CompleteSpace E] [Nontrivial E] :
    (ρclock (E := E)
        InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrixUnit01).comp
        (ρclock (E := E)
          InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrixUnit10) ≠
      (ρclock (E := E)
        InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrixUnit10).comp
        (ρclock (E := E)
          InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrixUnit01) := by
  intro h
  apply InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrix_units_noncommute
  apply ρclock_injective (E := E)
  rw [ρclock_mul, ρclock_mul]
  exact h

/-- Conjugation by the represented sheet swap exchanges the two matrix
Peirce projectors of the represented Krein grading. -/
theorem ρclock_matrixJ_conjugates_matrixEpsilon_projector_plus :
    (ρclock (E := E) matrixJ).comp
      (((ρclock (E := E)) ((1 / 2 : ℝ) •
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) + matrixEpsilon))).comp
        (ρclock (E := E) matrixJ)) =
      ρclock (E := E) ((1 / 2 : ℝ) •
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrixEpsilon)) := by
  rw [← ρclock_mul, ← ρclock_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixJ, matrixEpsilon, Matrix.mul_apply, Fin.sum_univ_two,
      smul_eq_mul] <;> ring

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixJ_conjugates_matrixEpsilon_projector_plus
#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrix_units_noncommute
