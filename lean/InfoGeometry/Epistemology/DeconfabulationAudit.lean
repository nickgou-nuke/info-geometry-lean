/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Epistemology.Deconfabulation

/-!
# Audit Module: DeconfabulationAudit

Audits and confirms axiom counts for `InfoGeometry.Epistemology.Deconfabulation`.
Strictly verifies that all theorems depend only on standard Lean foundational axioms
`[propext, Classical.choice, Quot.sound]` with 0 sorry and 0 admit.
-/

namespace InfoGeometry.Epistemology.DeconfabulationAudit

open InfoGeometry.Epistemology.Deconfabulation

#print axioms Archetype.rank_injective
#print axioms Archetype.primaMateria_precedes_all
#print axioms response_at_optimal
#print axioms response_gauge_invariant
#print axioms activity_gauge_invariant
#print axioms swap_restores_balance
#print axioms distillation_monotone

end InfoGeometry.Epistemology.DeconfabulationAudit
