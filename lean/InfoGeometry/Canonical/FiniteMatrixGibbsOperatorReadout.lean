import Mathlib.Tactic

import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

/-!
# Noncommutative matrix Gibbs operator readout

This file keeps the matrix Gibbs functional-calculus owner and the native
bounded-operator carrier distinct, connecting them through `matrixOp`.
No diagonalization or scalar Gibbs model is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout

open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ} [NeZero n]

def gibbsDensityOperator (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    FiniteOperatorAlgebra n :=
  matrixOp (gibbsDensity H hH β)

@[simp] theorem matrixOfOp_gibbsDensityOperator
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOfOp (gibbsDensityOperator H hH β) = gibbsDensity H hH β := by
  simp [gibbsDensityOperator]

theorem gibbsDensityOperator_matrixReadout_strictlyPositive
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    IsUnit (matrixOfOp (gibbsDensityOperator H hH β)) := by
  rw [matrixOfOp_gibbsDensityOperator]
  exact gibbsDensity_isUnit H hH β

theorem gibbsDensityOperator_trace_readout
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    finiteOperatorTrace (gibbsDensityOperator H hH β) =
      Matrix.trace (gibbsDensity H hH β) := by
  simp [finiteOperatorTrace, gibbsDensityOperator]

end InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout
