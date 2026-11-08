/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge

/-!
# Audit: `RealPeirceG2ColorActionBridge`

External `#check` audit verifying exported theorem and definition signatures for
`InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge`.
-/

namespace InfoGeometry.Synthesis.RealPeirceG2ColorActionBridgeAudit

open InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge

#check @realPeirce_colorMat3_noncomm
#check @peirceAlignedZornToGG
#check @peirceAlignedGGToZorn
#check @peirceAlignedZornToGG_left_inv
#check @peirceAlignedGGToZorn_right_inv
#check @peirceAlignedZornGGEquiv
#check @peirceAlignedZornToGG_add
#check @peirceAlignedZornToGG_smul
#check @realColorParameters
#check @zornG2Derivation_realColor_action
#check @peirceAlignedZornGGEquiv_intertwines_realColor
#check @peirceToFockOrderGG
#check @zornToLeptonQuarkMultiplet_eq_transition
#check @fockOrderGG_realColor_action
#check @peirceAndFockOrderCharts_differ
#check @sedenionPeirceAlignedToGG
#check @sedenionG2Derivation_realColor_action
#check @sedenionPeirceAligned_intertwines_realColor

#print axioms zornG2Derivation_realColor_action
#print axioms peirceAlignedZornGGEquiv_intertwines_realColor
#print axioms sedenionG2Derivation_realColor_action

end InfoGeometry.Synthesis.RealPeirceG2ColorActionBridgeAudit
