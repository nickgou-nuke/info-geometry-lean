/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.StateRadicalGNSIdealBridge

/-!
# Axiomatic Audit for State Radical GNS Ideal Bridge

Direct Lean 4 `#print axioms` query verifying that all theorems depend strictly
on standard Lean 4 core axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Canonical.StateRadicalGNSIdealBridge.Audit

open InfoGeometry.Canonical.StateRadicalGNSIdealBridge

#print axioms gnsRadical_is_left_ideal
#print axioms gns_left_action_well_defined
#print axioms gnsRadical_is_right_ideal_of_tracial
#print axioms gnsRadical_is_two_sided_ideal_of_tracial
#print axioms stateCommutator_eq_zero_iff_tracial
#print axioms non_tracial_of_stateCommutator_ne_zero

end InfoGeometry.Canonical.StateRadicalGNSIdealBridge.Audit
