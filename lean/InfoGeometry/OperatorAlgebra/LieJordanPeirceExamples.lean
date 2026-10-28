/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanTracePairing
import InfoGeometry.OperatorAlgebra.PeirceTracePairing
import InfoGeometry.OperatorAlgebra.OperatorDiracSchur

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

/-! The following dense 2×2 witnesses exercise the corrected Peirce and duality
owners added in the operator-algebra packet. They live in a nested namespace
so the established 3×3 regression API above remains intact. -/
namespace DensePeirceWitnesses

open Matrix
open InfoGeometry.OperatorAlgebra.LieJordanDuality
open InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
open InfoGeometry.Algebra.PeirceDeWittChiralSplit

def projection : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; 2, -1]
def firstOp : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
def secondOp : Matrix (Fin 2) (Fin 2) ℚ := !![2, 3; 5, 7]

theorem projection_idempotent : projection * projection = projection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, Matrix.mul_apply, Fin.sum_univ_two]

theorem inputs_noncommuting : firstOp * secondOp ≠ secondOp * firstOp := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [firstOp, secondOp, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem mixed_defect_nonzero :
    jordan ℚ (firstOp * secondOp - secondOp * firstOp) projection ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [jordan_apply, firstOp, secondOp, projection,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem weighted_pairing_nonsymmetric :
    trace (grading projection * firstOp * secondOp) ≠
      trace (grading projection * secondOp * firstOp) := by
  norm_num [grading, compIdempotent, projection, firstOp, secondOp,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

theorem source_complementary_identity :
    2 • peirce00 projection firstOp =
      2 • firstOp - jordan ℚ projection firstOp -
        ad ℚ projection (ad ℚ projection firstOp) := by
  exact twice_peirce00 ℚ projection_idempotent firstOp

theorem positive_sign_variant_false :
    2 • peirce00 projection firstOp ≠
      2 • firstOp - jordan ℚ projection firstOp +
        ad ℚ projection (ad ℚ projection firstOp) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [peirce00, compIdempotent, jordan_apply, ad_apply, projection, firstOp,
    two_nsmul, Matrix.mul_apply, Fin.sum_univ_two] at h00

end DensePeirceWitnesses

end InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples
