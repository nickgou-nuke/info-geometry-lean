/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceTraceForms
import InfoGeometry.OperatorAlgebra.LieJordanTraceDuality
import InfoGeometry.OperatorAlgebra.LieJordanDiracComposition

/-!
# Noncommuting regression witnesses

These full-matrix examples refute simplifications; they are not substitutes
for the arbitrary-algebra theorems. The Peirce projector is nondiagonal, the
transport and Jordan generators do not commute, and both Clifford generators
are nondiagonal. Rational calculations are certified by Lean tactics, not a
floating-point oracle.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan.Witnesses

open Matrix
open InfoGeometry.Algebra.PeirceDeWittChiralSplit
open scoped Matrix

abbrev M := Matrix (Fin 2) (Fin 2) ℚ

def projection : M := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]
def transport : M := !![0, 1; -1, 0]
def score : M := !![1, 1; 1, 0]
def observable : M := !![1, 2; 3, 4]
def probe : M := !![2, 1; -1, 3]
def gammaOne : M := !![0, 1; 1, 0]
def gammaTwo : M := !![5 / 3, 4 / 3; -4 / 3, -5 / 3]

theorem projection_idempotent : IsIdempotent projection := by
  change projection * projection = projection
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, Matrix.mul_apply, Fin.sum_univ_two]

theorem transport_score_noncommuting : transport * score ≠ score * transport := by
  intro h
  have h00 := congrArg (fun A : M => A 0 0) h
  norm_num [transport, score, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The dropped mixed term is demonstrably nonzero on a full matrix. -/
theorem mixed_term_nonzero :
    jordanOp ℚ (transport * score - score * transport) observable ≠ 0 := by
  intro h
  have h00 := congrArg (fun A : M => A 0 0) h
  norm_num [jordanOp_apply, transport, score, observable,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The source's proposed globally symmetric bilinear metric is not symmetric. -/
theorem weighted_trace_not_symmetric :
    weightedTrace projection observable probe ≠ weightedTrace projection probe observable := by
  norm_num [weightedTrace, grading, compIdempotent, projection, observable, probe,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- This pair satisfies the Clifford relations without being diagonal. -/
theorem actual_clifford_pair :
    gammaOne * gammaOne = 1 ∧ gammaTwo * gammaTwo = 1 ∧
      gammaOne * gammaTwo + gammaTwo * gammaOne = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gammaOne, gammaTwo, Matrix.mul_apply, Fin.sum_univ_two]

/-- A coefficient commutator in the actual plus action need not vanish. -/
theorem coefficient_defect_nonzero :
    (plus ℚ transport score * LinearMap.mulLeft ℚ gammaOne -
      LinearMap.mulLeft ℚ gammaOne * plus ℚ transport score) ≠ 0 := by
  rw [plus_coefficient_defect]
  intro h
  have hx := congrArg (fun T : Module.End ℚ M => (T 1) 0 0) h
  change (((transport + score) * gammaOne - gammaOne * (transport + score)) * 1) 0 0 = 0 at hx
  norm_num [transport, score, gammaOne, Matrix.mul_apply, Fin.sum_univ_two] at hx

end InfoGeometry.OperatorAlgebra.LieJordan.Witnesses
