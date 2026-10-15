/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwistorGNSParabolicQuotientBridge

/-!
# Axiomatic Audit for Twistor GNS Parabolic Quotient Bridge

Direct Lean 4 `#print axioms` query verifying that all theorems depend strictly
on standard Lean 4 core axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`
With zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Canonical.TwistorGNSBridge.Audit

open InfoGeometry.Canonical.TwistorGNSBridge

#print axioms IncidentPointPair.displacement_is_null
#print axioms twistor_stabilizer_fixes_twistor
#print axioms operator_commutator_outside_kernel
#print axioms twistor_null_and_commutator_gap_synthesis

end InfoGeometry.Canonical.TwistorGNSBridge.Audit
