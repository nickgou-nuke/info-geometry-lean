/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.SplitSedenionDerivationClassification

/-!
# Kernel Axiom Audit for `SplitSedenionDerivationClassification`

Verifies that the Full 14-Dimensional Split-Sedenion Derivation Classification
theorems (`sedenionDerivation_fst_sheet_snd_eq_zero`,
`sedenionDerivation_snd_sheet_fst_eq_zero`,
`sedenionDerivation_snd_sheet_snd_eq_fst_sheet_fst`,
`sedenionDerivation_eq_cdLift_fst`,
`sedenionDerivation_eq_sedenionG2Derivation`,
`sedenionDerivation_existsUnique_g2Params`,
`sedenionDerivation_iff_starDerivation`,
`sedenionDerivation_sedenionEll_eq_zero`) depend exclusively on the standard
Lean 4 kernel axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.Synthesis.SplitSedenionDerivationClassificationAudit

open InfoGeometry.Synthesis.SplitSedenionDerivationClassification

#check @od1_linear_eq_zero
#check @zornVZ_right_antiassociator_eq_zero
#check @zornVZ_left_nucleus_trace_zero_eq_zero
#check @sedenionDerivation_fst_sheet_snd_eq_zero
#check @sedenionDerivation_snd_sheet_fst_eq_zero
#check @sedenionDerivation_fst_sheet_fst_leibniz
#check @sedenionDerivation_snd_sheet_snd_eq_fst_sheet_fst
#check @sedenionDerivation_eq_cdLift_fst
#check @sedenionToVDer
#check @derivationParameters_sedenionToVDer
#check @sedenionDerivation_eq_sedenionG2Derivation
#check @sedenionDerivation_existsUnique_g2Params
#check @sedenionDerivation_iff_starDerivation
#check @sedenionDerivation_sedenionEll_eq_zero

#print axioms od1_linear_eq_zero
#print axioms zornVZ_right_antiassociator_eq_zero
#print axioms zornVZ_left_nucleus_trace_zero_eq_zero
#print axioms sedenionDerivation_fst_sheet_snd_eq_zero
#print axioms sedenionDerivation_snd_sheet_fst_eq_zero
#print axioms sedenionDerivation_fst_sheet_fst_leibniz
#print axioms sedenionDerivation_snd_sheet_snd_eq_fst_sheet_fst
#print axioms sedenionDerivation_eq_cdLift_fst
#print axioms sedenionDerivation_eq_sedenionG2Derivation
#print axioms sedenionDerivation_existsUnique_g2Params
#print axioms sedenionDerivation_iff_starDerivation
#print axioms sedenionDerivation_sedenionEll_eq_zero

end InfoGeometry.Synthesis.SplitSedenionDerivationClassificationAudit
