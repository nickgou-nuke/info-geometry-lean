/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge

/-!
# Audit: `Cl55TwistorLinearEquivAndOrderFourBridge`

Typecheck and signature audit for `InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge`.
-/

namespace InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge.Audit

open InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge

#check @twistor55ToSplitSedenion_smul
#check @twistor55SplitSedenionLinearEquiv
#check @cl44MatrixLeftIdealTwistor55LinearEquiv
#check @zornToLeptonQuarkMultiplet_smul
#check @zornLeptonQuarkLinearEquiv
#check @sedenionAndreevSheetSwap_sedenionOne_ne
#check @sedenionAndreevSheetSwap_sq_sedenionOne_ne
#check @sedenionAndreevSheetSwap_cube_sedenionOne_ne
#check @sedenionAndreevSheetSwap_exact_minimal_period_four
#check @canonicalSuperTwistor55
#check @superAndreevReflect_canonical_ne
#check @superAndreevReflect_sq_canonical_ne
#check @superAndreevReflect_cube_canonical_ne
#check @superAndreevReflect_exact_minimal_period_four
#check @twistor55SedenionMul
#check @twistor55SedenionMul_add_left
#check @twistor55SedenionMul_add_right
#check @twistor55SedenionMul_smul_left
#check @twistor55SedenionMul_smul_right
#check @exists_twistor55Sedenion_zero_divisors
#check @exists_twistor55Sedenion_nonzero_associator

end InfoGeometry.Synthesis.Cl55TwistorLinearEquivAndOrderFourBridge.Audit
