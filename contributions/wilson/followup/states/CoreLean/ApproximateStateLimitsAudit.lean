/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import CoreLean.ApproximateStateLimits

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-! # Axiom audit of summable approximate compatibility -/

public section

#print axioms ApproximateCompatibility.evaluationSequence
#print axioms ApproximateCompatibility.evaluationSequence_zero
#print axioms ApproximateCompatibility.evaluationSequence_succ
#print axioms ApproximateCompatibility.dist_evaluationSequence_succ_le
#print axioms ApproximateCompatibility.cauchySeq_evaluationSequence
#print axioms ApproximateCompatibility.exists_compatible_limit
#print axioms ApproximateCompatibility.evaluationSequence_add
#print axioms ApproximateCompatibility.evaluationSequence_smul
#print axioms ApproximateCompatibility.evaluationSequence_one
#print axioms ApproximateCompatibility.evaluationSequence_nonneg
#print axioms ApproximateCompatibility.exists_normalized_positive_limits
