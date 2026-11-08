/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.TodorovSplitOctonionStandardModelBerezinianBridge

/-!
# Audit: `TodorovSplitOctonionStandardModelBerezinianBridge`

Typecheck and signature audit for `InfoGeometry.Synthesis.TodorovSplitOctonionStandardModelBerezinianBridge`.
-/

namespace InfoGeometry.Synthesis.TodorovSplitOctonionStandardModelBerezinianBridge.Audit

open InfoGeometry.Synthesis.TodorovSplitOctonionStandardModelBerezinianBridge

#check @zornHyperbolicOmega
#check @zornHyperbolicOmega_properties
#check @zornIdemPlus
#check @zornIdemMinus
#check @zorn_todorov_idempotent_socle_decomposition
#check @embedUpperChiral
#check @embedLowerChiral
#check @zorn_peirce_quark_triplet_absorption
#check @zornG2Derivation_zornHyperbolicOmega_eval
#check @zornG2Derivation_zornHyperbolicOmega_eq_zero_iff
#check @zornG2Derivation_stabilizer_annihilates_leptons
#check @todorov_g2_to_su3_color_dimension_reduction
#check @berezinianLeptonQuarkScale
#check @berezinianLeptonQuarkScale_invariants
#check @bmsCelestialSupertranslation
#check @bmsCelestialSupertranslation_interval_invariant

end InfoGeometry.Synthesis.TodorovSplitOctonionStandardModelBerezinianBridge.Audit
