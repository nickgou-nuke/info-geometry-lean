/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge

/-!
# Audit Companion for `Cl55TwistorSplitSedenionColorBridge`

Verifies that every theorem in `InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge`
type-checks in the Lean 4 kernel and depends only on the standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridgeAudit

open InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge

#check @twistor55ToSplitSedenion_splitSedenionToTwistor55
#check @splitSedenionToTwistor55_twistor55ToSplitSedenion
#check @twistor55SplitSedenionEquiv
#check @twistor55ToSplitSedenion_add
#check @cl44MatrixLeftIdealTwistor55Equiv
#check @zornToLeptonQuarkMultiplet_leptonQuarkMultipletToZorn
#check @leptonQuarkMultipletToZorn_zornToLeptonQuarkMultiplet
#check @zornLeptonQuarkEquiv
#check @zornToLeptonQuarkMultiplet_add
#check @zornNorm_eq_gunaydin_gursey_coordinates
#check @zornToFin8_neg_one_smul
#check @splitSedenionToTwistor55_sedenionAndreevSheetSwap
#check @sedenionAndreevSheetSwap_sq
#check @sedenionAndreevSheetSwap_order_four
#check @sedenionNorm_sedenionAndreevSheetSwap

#print axioms twistor55SplitSedenionEquiv
#print axioms cl44MatrixLeftIdealTwistor55Equiv
#print axioms zornLeptonQuarkEquiv
#print axioms sedenionAndreevSheetSwap_order_four
#print axioms sedenionNorm_sedenionAndreevSheetSwap

end InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridgeAudit
