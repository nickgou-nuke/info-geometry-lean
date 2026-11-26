/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SplitCliffordSuperGrassmannianColimit

/-!
# Audit Companion for Dimension Formulae and Scalar Difference Identities

Module: `InfoGeometry.SuperGrassmannian.SplitCliffordSuperGrassmannianColimitAudit`

This module audits the axiomatic footprint of all theorems in
`SplitCliffordSuperGrassmannianColimit.lean`.
-/

namespace InfoGeometry.SuperGrassmannian.SplitCliffordColimit.Audit

open InfoGeometry.SuperGrassmannian.SplitCliffordColimit

-- Section 1: Natural-Number Formulae
#print axioms clifford_dim_eq_two_pow_two_n
#print axioms spinor_sq_eq_clifford
#print axioms chiral_split_sum

-- Section 2: Formula Evaluations at Parameters Four and Eight
#print axioms stage_four_dimension_formula_agreement
#print axioms stage_eight_dimension_formula_identity

-- Section 3: Parity Identities
#print axioms chiral_half_dim_even
#print axioms chiral_half_dimension_sign_even

-- Section 4: Scalar Normalization Formulae
#print axioms normalized_identity_trace_eq_one
#print axioms normalized_scalar_factor_four_cancellation

-- Section 5: Equal-Shift Integer-Difference Arithmetic
#print axioms equal_shift_preserves_dimension_difference

end InfoGeometry.SuperGrassmannian.SplitCliffordColimit.Audit
