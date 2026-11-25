/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import CoreLean.CutoffRecursion
public import CoreLean.CutoffLimit

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-! Explicit axiom audit for the cutoff comparison endpoint. -/

#print axioms CoreLean.CutoffComparison.normalized_sub
#print axioms CoreLean.CutoffComparison.norm_normalized_sub_le
#print axioms CoreLean.CutoffComparison.norm_exp_mul_sub_le
#print axioms CoreLean.CutoffComparison.exists_limit_of_relative_errors
#print axioms CoreLean.CutoffRecursion.le_weight_of_monotone_homogeneous
#print axioms CoreLean.CutoffRecursion.le_weight_of_row_bound
#print axioms CoreLean.CutoffRecursion.le_two_mul_weight_of_quarter_row_bound
#print axioms CoreLean.CutoffSummability.log_affine_isBigO_log
#print axioms CoreLean.CutoffSummability.log_affine_rpow_isBigO_rpow
#print axioms CoreLean.CutoffSummability.log_affine_pow_isBigO_rpow
#print axioms CoreLean.CutoffSummability.summable_rpow_mul_log_affine_rpow
#print axioms CoreLean.CutoffSummability.summable_rpow_mul_log_affine_pow
#print axioms CoreLean.CutoffSummability.summable_cutoff_remainder
#print axioms CoreLean.CutoffSummability.summable_cutoff_remainder_mul_cutoff
#print axioms CoreLean.CutoffLimit.summable_linearLossRemainder
#print axioms CoreLean.CutoffLimit.exists_limit_of_cutoff_remainder
