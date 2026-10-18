/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge

/-!
# Audit Companion for `Cl44MinimalIdealInducedSedenionProductBridge`

Verifies that every theorem in `InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge`
type-checks in the Lean 4 kernel and depends only on the standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridgeAudit

open InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge

#check @instAddCommGroupZornSplitOctonion
#check @instModuleZornSplitOctonion
#check @spinor16ToSplitSedenion_smul
#check @spinor16SplitSedenionLinearEquiv
#check @cl44MatrixLeftIdealSplitSedenionLinearEquiv
#check @idealSedenionConj_involutive
#check @exists_idealSedenion_zero_divisors
#check @exists_idealSedenion_nonzero_associator
#check @sedenionMul_add_left
#check @sedenionMul_add_right
#check @sedenionMul_smul_left
#check @sedenionMul_smul_right
#check @idealSedenionMul_add_left
#check @idealSedenionMul_add_right
#check @idealSedenionMul_smul_left
#check @idealSedenionMul_smul_right
#check @sedenionMul_sedenionConj
#check @sedenionNorm_eq_zero_iff_sedenionMul_sedenionConj_eq_zero
#check @idealSedenion_norm_zero_iff_mul_conj_zero
#check @idealSedenionEll_sq_eq_one
#check @idealG2Derivation_leibniz
#check @idealG2Derivation_conj
#check @idealG2Derivation_ell_zero
#check @readIdealG2Params_idealG2Derivation
#check @idealG2Derivation_injective
#check @ideal_product_is_non_associative
#check @ideal_norm_zero_iff_mul_conj_zero

#print axioms cl44MatrixLeftIdealSplitSedenionLinearEquiv
#print axioms idealSedenionMul_add_left
#print axioms idealSedenionMul_smul_left
#print axioms sedenionMul_sedenionConj
#print axioms idealSedenion_norm_zero_iff_mul_conj_zero
#print axioms idealG2Derivation_leibniz
#print axioms idealG2Derivation_injective
#print axioms ideal_product_is_non_associative
#print axioms ideal_norm_zero_iff_mul_conj_zero

end InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridgeAudit
