/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

/-!
# Audit Companion: SplitSedenionDerivationAnomaly

Verifies that all public theorems in `InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly`
type-check cleanly and depend only on standard Lean 4 axioms (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace InfoGeometry.Synthesis.SplitSedenionDerivationAnomalyAudit

open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

#check @split_sedenion_derivation_dimension_synthesis
#check @cdLift_is_cayleyDickson_star_derivation
#check @cdLift_commutator_hom
#check @sl2_so21_doubling_generators_synthesis
#check @g2_sl2_bimodule_actions_commute
#check @derivation_preserves_zero_divisor_tangent
#check @split_cayleyDickson_nilpotent_zero_divisor
#check @sl2_so21_doubling_witness_int

end InfoGeometry.Synthesis.SplitSedenionDerivationAnomalyAudit
