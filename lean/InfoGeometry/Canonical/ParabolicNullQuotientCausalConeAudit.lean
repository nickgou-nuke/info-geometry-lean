/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ParabolicNullQuotientCausalCone

/-!
# Axiomatic Audit for Parabolic Null Quotient and Causal Cone

Direct Lean 4 `#print axioms` query verifying that all theorems depend strictly
on standard Lean 4 core axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Canonical.ParabolicQuotient.Audit

open InfoGeometry.Canonical.ParabolicQuotient

#print axioms nullKernel_is_isotropic
#print axioms bilinForm_congr_nullKernel
#print axioms commutator_image_zero_iff_commute
#print axioms quantum_shield_commutator_non_vanishing
#print axioms coneLe_refl
#print axioms coneLe_trans
#print axioms nullVectorStabilizer
#print axioms causal_cone_monotone

end InfoGeometry.Canonical.ParabolicQuotient.Audit
