/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.KaplanskyZeroDivisorArchetype

/-!
# Axiomatic Audit for Kaplansky Zero Divisor Archetypes

This companion module queries the Lean 4 kernel directly using `#print axioms` to
guarantee that all proved lemmas depend strictly on standard Lean 4 core axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`

And confirms zero reliance on `sorry`, `admit`, or custom axioms.
-/

namespace InfoGeometry.Algebra.KaplanskyZeroDivisor.Audit

open InfoGeometry.Algebra.KaplanskyZeroDivisor

#print axioms idempotent_complement
#print axioms idempotent_mul_complement_self
#print axioms idempotent_non_trivial_factors
#print axioms charTwo_involution_add_one_is_nilpotent
#print axioms charTwo_involution_add_one_ne_zero
#print axioms idempotent_yields_zero_divisor_pair
#print axioms charTwo_involution_yields_zero_divisor_pair
#print axioms charTwo_sum_ones_even

end InfoGeometry.Algebra.KaplanskyZeroDivisor.Audit
