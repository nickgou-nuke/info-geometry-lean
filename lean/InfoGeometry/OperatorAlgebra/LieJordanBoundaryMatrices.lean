/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
import InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Full-matrix positivity and noncommuting obstruction witnesses

The cross action is positive when the second coefficient is the adjoint of the
first. Trace preservation has a separate normalization hypothesis. General
pairs have neither property by default. The explicit off-diagonal witnesses
below test failures of stronger claims; they do not replace the general algebra.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanBoundaryMatrices

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix
open scoped Matrix
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Native positivity for the adjoint-paired two-sided map on all real matrices. -/
theorem crossTransport_posSemidef (u x : Matrix n n ℝ) (hx : x.PosSemidef) :
    (crossTransport (R := ℝ) u uᴴ x).PosSemidef := by
  exact (hx.mul_mul_conjTranspose_same u).add (hx.conjTranspose_mul_mul_same u)

/-- Positive semidefinite, not necessarily invertible or strictly positive. -/
theorem adjoint_quadratic_posSemidef (u : Matrix n n ℝ) :
    (u * uᴴ + uᴴ * u).PosSemidef :=
  (Matrix.posSemidef_self_mul_conjTranspose u).add
    (Matrix.posSemidef_conjTranspose_mul_self u)

theorem adjoint_cross_trace (u x : Matrix n n ℝ) :
    Matrix.trace (crossTransport (R := ℝ) u uᴴ x) =
      Matrix.trace ((u * uᴴ + uᴴ * u) * x) :=
  trace_crossTransport (R := ℝ) (Matrix.traceAddMonoidHom n ℝ)
    Matrix.trace_mul_comm u uᴴ x

theorem adjoint_cross_trace_preserving (u x : Matrix n n ℝ)
    (hnorm : u * uᴴ + uᴴ * u = 1) :
    Matrix.trace (crossTransport (R := ℝ) u uᴴ x) = Matrix.trace x := by
  rw [adjoint_cross_trace, hnorm, one_mul]

/-- This normalization is exactly unitality of this particular map. -/
theorem adjoint_cross_unital_iff (u : Matrix n n ℝ) :
    crossTransport (R := ℝ) u uᴴ 1 = 1 ↔ u * uᴴ + uᴴ * u = 1 := by
  rw [crossTransport_one]

/-- A non-diagonal idempotent for a counterexample inside actual Peirce corners. -/
def cornerWitnessP : M := !![1, 1, 0; 0, 0, 0; 0, 0, 1]
def cornerWitnessV : M := transportS - transportH * transportS
def cornerWitnessX : M := observableX - observableX * transportH

theorem cornerWitnessP_idempotent : cornerWitnessP * cornerWitnessP = cornerWitnessP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cornerWitnessP, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cornerWitness_upper : peirce10 cornerWitnessP transportH = transportH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [peirce10, compIdempotent, cornerWitnessP, transportH,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem cornerWitness_lower : peirce01 cornerWitnessP cornerWitnessV = cornerWitnessV := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [peirce01, compIdempotent, cornerWitnessP, cornerWitnessV, transportH, transportS,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The error persists for opposite corners of a non-diagonal idempotent.
Both coefficients and the tested observable are off-diagonal matrices. -/
theorem mixed_difference_without_defect_false :
    ⁅transportH, cornerWitnessV * cornerWitnessX + cornerWitnessX * cornerWitnessV⁆ -
      ⁅cornerWitnessV, transportH * cornerWitnessX + cornerWitnessX * transportH⁆ ≠
    (transportH * cornerWitnessV - cornerWitnessV * transportH) * cornerWitnessX +
      cornerWitnessX * (transportH * cornerWitnessV - cornerWitnessV * transportH) := by
  intro hz
  have h := congrArg (fun m : M => m 1 1) hz
  norm_num [Ring.lie_def, cornerWitnessV, cornerWitnessX, transportH, transportS, observableX,
    Matrix.mul_apply, Fin.sum_univ_succ] at h

theorem transportH_square_zero : transportH * transportH = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transportH, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A square-zero coefficient need not induce a square-zero adjoint operator. -/
theorem square_zero_coefficient_nonzero_ad_square :
    ⁅transportH, ⁅transportH, lowerY⁆⁆ ≠ 0 := by
  intro hz
  have h := congrArg (fun m : M => m 0 1) hz
  norm_num [Ring.lie_def, transportH, lowerY,
    Matrix.mul_apply, Fin.sum_univ_succ] at h

/-- Pair-generated centrality does not imply ambient centrality. -/
theorem quadratic_not_ambient_central :
    ⁅upperX * lowerY + lowerY * upperX, transportS⁆ ≠ 0 := by
  intro hz
  have h := congrArg (fun m : M => m 1 2) hz
  norm_num [Ring.lie_def, upperX, lowerY, transportS,
    Matrix.mul_apply, Fin.sum_univ_succ] at h

end InfoGeometry.OperatorAlgebra.LieJordanBoundaryMatrices
