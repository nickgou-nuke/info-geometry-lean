/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl44PrimitiveIdempotentIdeal

/-!
# Audit Companion: Cl44PrimitiveIdempotentIdeal

Verifies that all public theorems in `InfoGeometry.Cl44IdempotentIdeal`
type-check cleanly and depend only on standard Lean 4 axioms (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace InfoGeometry.Synthesis.Cl44PrimitiveIdempotentIdealAudit

open InfoGeometry.Cl44IdempotentIdeal

#check @primIdem_mul_self
#check @primIdem_ne_zero
#check @uWitt0_mul_vWitt0_ne_comm
#check @uWitt_mul_primIdem_zero
#check @left_ideal_closed
#check @leftIdealEquiv
#check @semiSpinor_disjoint
#check @semiSpinor_span_top
#check @even_states_card
#check @odd_states_card

end InfoGeometry.Synthesis.Cl44PrimitiveIdempotentIdealAudit
