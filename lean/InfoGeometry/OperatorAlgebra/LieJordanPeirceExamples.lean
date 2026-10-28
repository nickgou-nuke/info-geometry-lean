/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanTracePairing

/-!
# Noncommuting regression witnesses

General results are proved in the owner modules, not inferred from these
examples. All three transport inputs are off-diagonal 3-by-3 matrices. The
weighted-trace example uses an oblique, non-diagonal idempotent.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples

open Matrix
open InfoGeometry.OperatorAlgebra.LieJordanDualTransport

abbrev M := Matrix (Fin 3) (Fin 3) ℚ

def transportH : M := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
def transportS : M := !![0, 0, 0; 0, 0, 1; 0, 0, 0]
def observableX : M := !![0, 0, 0; 0, 0, 0; 1, 0, 0]

theorem coefficient_commutator_nonzero :
    transportH * transportS - transportS * transportH ≠ 0 := by
  intro hz
  have h := congrArg (fun m : M => m 0 2) hz
  norm_num [transportH, transportS, Matrix.mul_apply, Fin.sum_univ_succ] at h

/-- Direct unequal-product form of the coefficient commutator witness. -/
theorem coefficient_products_noncommute :
    transportH * transportS ≠ transportS * transportH := by
  intro hz
  have h := congrArg (fun m : M => m 0 2) hz
  norm_num [transportH, transportS, Matrix.mul_apply, Fin.sum_univ_succ] at h

/-- The correction rejected by the commuting reduction is genuinely nonzero. -/
theorem composition_order_defect_nonzero :
    minus (R := ℚ) transportH transportS (plus (R := ℚ) transportH transportS observableX) -
      plus (R := ℚ) transportH transportS (minus (R := ℚ) transportH transportS observableX) ≠ 0 := by
  intro hz
  have h := congrArg (fun m : M => m 0 0) hz
  norm_num [plus_apply, minus_apply, transportH, transportS, observableX,
    Matrix.mul_apply, Fin.sum_univ_succ] at h

def obliqueP : M := !![1, 1, 0; 0, 0, 0; 0, 0, 0]
def upperX : M := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
def lowerY : M := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

theorem obliqueP_idempotent : obliqueP * obliqueP = obliqueP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueP, Matrix.mul_apply, Fin.sum_univ_succ]

/-- An explicit witness against interpreting the weighted bilinear form as a
symmetric metric on all operators. -/
theorem weighted_trace_not_symmetric :
    Matrix.trace ((obliqueP - (1 - obliqueP)) * upperX * lowerY) ≠
      Matrix.trace ((obliqueP - (1 - obliqueP)) * lowerY * upperX) := by
  norm_num [obliqueP, upperX, lowerY, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_succ]

end InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples
