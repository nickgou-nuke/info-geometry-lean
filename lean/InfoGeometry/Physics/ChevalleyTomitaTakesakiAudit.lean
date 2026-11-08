/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ChevalleyTomitaTakesaki

/-!
# Audit: ChevalleyTomitaTakesakiAudit

Automated kernel verification of the Chevalley dyad index relabeling:
- Zero debt: 0 sorry, 0 admit, 0 custom axioms.
- Verifies the involutive index relabeling.
- Verifies diagonal swap: vacuum $\leftrightarrow$ excited idempotents $E_{00} \leftrightarrow E_{11}$.
- Verifies off-diagonal swap: transition dyads $E_{01} \leftrightarrow E_{10}$ (equivalently $u \leftrightarrow v$).
- Verifies preservation of the resolution of unity.
- Verifies the master dyad relabeling theorem. No modular-theory structure is assumed.
- Axiom footprint check: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.ChevalleyTomitaTakesakiAudit

open CategoryTheory
open InfoGeometry.Physics.ChevalleyDyads
open InfoGeometry.Physics.ChevalleyTomitaTakesaki

set_option linter.unusedVariables false

-- 1. Signature and Type-Level Verification
#check @mirrorIdx_involutive
#check @mirrorIdx_swaps_transition
#check @mirrorIdx_swaps_diagonal
#check @mirrorIdx_neq_self
#check @mirrorDyad_00_eq_E11
#check @mirrorDyad_11_eq_E00
#check @mirrorDyad_01_eq_E10
#check @mirrorDyad_10_eq_E01
#check @mirrorDyad_involutive
#check @mirror_resolution_of_unity
#check @mirror_swaps_car_nilpotents
#check @master_tomitakesaki_mirror_soundness

-- 2. Axiom Footprint Verification
#print axioms mirrorIdx_involutive
#print axioms mirrorIdx_swaps_transition
#print axioms mirrorIdx_swaps_diagonal
#print axioms mirrorIdx_neq_self
#print axioms mirrorDyad_00_eq_E11
#print axioms mirrorDyad_11_eq_E00
#print axioms mirrorDyad_01_eq_E10
#print axioms mirrorDyad_10_eq_E01
#print axioms mirrorDyad_involutive
#print axioms mirror_resolution_of_unity
#print axioms mirror_swaps_car_nilpotents
#print axioms master_tomitakesaki_mirror_soundness

end InfoGeometry.Physics.ChevalleyTomitaTakesakiAudit
