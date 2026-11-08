/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge

/-!
# Audit: `ShirokovCliffordTraceDetInverseBridge`

Typecheck and signature audit for `InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge`.
-/

namespace InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge.Audit

open InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge

#check @cl11GenE0
#check @cl11GenE1
#check @cl11GenE01
#check @cl11GenE0_mul_cl11GenE1_ne_comm
#check @cl11Multivector
#check @cl11ShirokovTrace
#check @cl11Multivector_trace_eq
#check @cl11ShirokovTrace_multivector
#check @cl11ShirokovTrace_mul_comm
#check @cl11GradeInvol
#check @cl11Reversion
#check @cl11CliffordConj
#check @cl11ShirokovTrace_invariance
#check @cl11DetScalar
#check @cl11_cliffordConj_mul_multivector
#check @cl11_shirokov_det_formula
#check @cl11_shirokov_inverse_formula
#check @cl22E0
#check @cl22E1
#check @cl22E0_mul_cl22E1_ne_comm
#check @cl22ShirokovTrace
#check @cl22ShirokovTrace_weylScaledMultivector
#check @cl22ShirokovTrace_mul_comm
#check @cl22_det_mul
#check @cl22_det_smul_degree_four
#check @weylScaledSolderedVector_shirokov_inverse

end InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge.Audit
