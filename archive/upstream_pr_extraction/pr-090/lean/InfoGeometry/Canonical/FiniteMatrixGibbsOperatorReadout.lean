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

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def gibbsDensityOperator (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    FiniteOperatorAlgebra n :=
  matrixOp (gibbsDensity H hH β)

@[simp] theorem matrixOfOp_gibbsDensityOperator
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOfOp (gibbsDensityOperator H hH β) = gibbsDensity H hH β := by
  simp [gibbsDensityOperator]

theorem gibbsDensityOperator_matrixReadout_strictlyPositive
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    IsStrictlyPositive (matrixOfOp (gibbsDensityOperator H hH β)) := by
  rw [matrixOfOp_gibbsDensityOperator]
  exact gibbsDensity_strictlyPositive H hH β

theorem gibbsDensityOperator_trace_readout
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    finiteOperatorTrace (gibbsDensityOperator H hH β) =
      Matrix.trace (gibbsDensity H hH β) := by
  rfl

end InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout
