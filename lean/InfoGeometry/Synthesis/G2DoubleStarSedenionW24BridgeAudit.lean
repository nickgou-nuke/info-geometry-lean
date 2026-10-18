/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge

/-!
# Axiom Audit for `InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge`

Kernel-level `#print axioms` verification confirming that all declarations in
`InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge` depend exclusively on standard Lean 4
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace InfoGeometry.Synthesis.G2DoubleStarSedenionW24BridgeAudit

open InfoGeometry.Synthesis.G2DoubleStarSedenionW24Bridge

#print axioms DoubleStarSheetCarrier
#print axioms doubleStarSheetCarrier_card
#print axioms doubleStarSheetCarrierEquivFin24
#print axioms phi24Eval_eq_phi12Eval_sq
#print axioms phi24Eval_eq_zero_of_phi12Eval_sq_eq_zero
#print axioms sheetSwapLift
#print axioms sheetSwapLift_sq_apply
#print axioms split_cayleyDickson_plus_minus_square_zero
#print axioms cdLift_preserves_square_zero_tangent
#print axioms sedenion_plus_minus_diagonal_norm_zero

end InfoGeometry.Synthesis.G2DoubleStarSedenionW24BridgeAudit
