/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GradedDMPResolution
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A noncommuting real matrix witness with a nonzero nilpotent summand

The full matrices, including both generalized inverses, are evaluated exactly.
The regular corner is not scalar, the spectral support is oblique, and both
the MP commutator and the DMP/MPD difference are nonzero. The square of that
odd difference is nonzero as well. No scalar or simultaneous diagonal model
stands in for the operator statements.
-/

noncomputable section

namespace InfoGeometry.Canonical.GradedDMPMatrixWitness

open Matrix
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinMoorePenrosePartition
open InfoGeometry.Canonical.GradedDMPResolution
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.IdempotentCartan

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def forward : Mat := !![1, 1, -1, 0; 0, 2, 0, -2; 0, 0, 0, 1; 0, 0, 0, 0]
def drazin : Mat :=
  !![1, -(1/2), -1, 1/2; 0, 1/2, 0, -(1/2); 0, 0, 0, 0; 0, 0, 0, 0]
def metric : Mat :=
  !![1/2, -(1/4), -(1/2), 0; 0, 1/2, 1, 0;
     -(1/2), 1/4, 1/2, 0; 0, 0, 1, 0]

/-- All three indexed Drazin equations hold, with witness exponent two. -/
theorem drazin_witness : IsDrazinInverse forward drazin 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [forward, drazin, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

/-- The displayed metric inverse satisfies all four Penrose equations. -/
theorem metric_witness : IsMoorePenroseInverse forward metric := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [forward, metric, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The complement contains a nonzero square-zero operator. -/
theorem nilpotent_part_square_zero : (fittingNilpotentPart forward drazin) ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fittingNilpotentPart, complementaryProjection, projection,
      forward, drazin, pow_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem nilpotent_part_ne_zero : fittingNilpotentPart forward drazin ≠ 0 := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 3) h
  norm_num [fittingNilpotentPart, complementaryProjection, projection,
    forward, drazin, Matrix.mul_apply, Fin.sum_univ_succ] at hc

/-- Noncommutativity is witnessed by the actual original and metric-inverse matrices. -/
theorem forward_metric_noncommute : forward * metric ≠ metric * forward := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 2) h
  norm_num [forward, metric, Matrix.mul_apply, Fin.sum_univ_succ] at hc

theorem spectral_support_oblique : star (projection forward drazin) ≠ projection forward drazin := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 2) h
  norm_num [projection, forward, drazin, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Fin.sum_univ_succ] at hc

theorem ordered_inverses_distinct :
    dmpInverse forward drazin metric ≠ dualDmpInverse forward drazin metric := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 0) h
  norm_num [dmpInverse, dualDmpInverse, forward, drazin, metric,
    Matrix.mul_apply, Fin.sum_univ_succ] at hc

/-- The general equivalence detects a genuine odd metric-inverse component. -/
theorem metric_odd_part_ne_zero : oddPart (projection forward drazin) metric ≠ 0 := by
  intro h
  exact ordered_inverses_distinct ((dmp_eq_dual_iff_odd_zero drazin_witness).2 h)

/-- An odd sum is not generally square-zero, even though its directed corners are. -/
theorem ordered_difference_square_ne_zero :
    (dmpInverse forward drazin metric - dualDmpInverse forward drazin metric) ^ 2 ≠ 0 := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 3) h
  norm_num [dmpInverse, dualDmpInverse, forward, drazin, metric,
    pow_two, Matrix.mul_apply, Fin.sum_univ_succ] at hc

/-- The outer inverse cannot reconstruct the nonzero complementary summand. -/
theorem dmp_not_inner_inverse : forward * dmpInverse forward drazin metric * forward ≠ forward := by
  intro h
  exact nilpotent_part_ne_zero
    ((dmp_inner_iff_nilpotent_part_zero drazin_witness metric_witness).1 h)

end InfoGeometry.Canonical.GradedDMPMatrixWitness
