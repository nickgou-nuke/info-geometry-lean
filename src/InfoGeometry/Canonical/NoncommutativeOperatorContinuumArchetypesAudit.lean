/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NoncommutativeOperatorContinuumArchetypes

/-!
# Axiomatic Audit for Non-Commutative Operator Continuum Archetypes

Direct Lean 4 `#print axioms` query verifying that all theorems depend strictly
on standard Lean 4 core axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Canonical.NoncommutativeContinuum.Audit

open InfoGeometry.Canonical.NoncommutativeContinuum

#print axioms CuntzPair.e₁_idempotent
#print axioms CuntzPair.e₂_idempotent
#print axioms CuntzPair.e₁_mul_e₂_zero
#print axioms CuntzPair.e₂_mul_e₁_zero
#print axioms CuntzPair.e₂_eq_one_sub_e₁
#print axioms CuntzPair.s₁_not_unitary
#print axioms braid_commutant
#print axioms inv_braid_eq
#print axioms isModularInvariant_zero
#print axioms isModularInvariant_one
#print axioms isModularInvariant_add
#print axioms isModularInvariant_mul
#print axioms modular_flow_non_trivial_iff
#print axioms injective_hom_kernel_trivial
#print axioms causalPast_monotone

end InfoGeometry.Canonical.NoncommutativeContinuum.Audit
