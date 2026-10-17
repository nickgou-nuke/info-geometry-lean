/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis

/-!
# Categorical Inevitability Poset Synthesis — Axiom & Kernel Audit

Verifies via `#print axioms` that every declaration in
`InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis` depends only on the
standard Lean 4 foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesisAudit

open InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis

#print axioms fisherMetric_smul_left
#print axioms scaledFisher_represents_covector_iff
#print axioms chentsov_unique_scale_and_steepest_ascent
#print axioms abstractNullPlus
#print axioms abstractNullMinus
#print axioms abstractNullPlus_eq_abstractWittPlus
#print axioms abstractNullMinus_eq_abstractWittMinus
#print axioms cl11MatrixAlgEquiv_abstractNullPlus
#print axioms cl11MatrixAlgEquiv_abstractNullMinus
#print axioms abstractNullPlus_sq_zero
#print axioms abstractNullMinus_sq_zero
#print axioms abstractNullPlus_anticomm_abstractNullMinus
#print axioms abstractNullPlus_sub_abstractNullMinus_eq_ι_eMinus
#print axioms abstractNullPlus_add_abstractNullMinus_eq_ι_ePlus
#print axioms paraKahler_projPlus_projPlus_zero
#print axioms paraKahler_projMinus_projMinus_zero
#print axioms paraKahler_metric_eq_offDiagonal_pairing
#print axioms paraKahler_self_metric_eq_two_mul_cross_sheet
#print axioms apply_eq_paraProjectorPlus_sub_paraProjectorMinus
#print axioms omega_eq_g_comp_K
#print axioms paraKahler_symplectic_eq_offDiagonal_pairing
#print axioms IsMobiusTwist
#print axioms mobiusTwist_apply_comm
#print axioms mobiusTwist_maps_tplus_to_tminus
#print axioms mobiusTwist_maps_tminus_to_tplus
#print axioms mobiusTwist_intertwines_paraProjectorPlus
#print axioms mobiusTwist_intertwines_paraProjectorMinus
#print axioms IsSheetSwapInvolution
#print axioms sheetSwapInvolution_apply_sq
#print axioms inducedComplexStructure
#print axioms inducedComplexStructure_sq_eq_neg_id
#print axioms inducedComplexStructure_isMobiusTwist
#print axioms inducedComplexStructure_metric_neg
#print axioms inducedComplexStructure_symplectic_invariant
#print axioms swapSheetInvolution
#print axioms swapSheetInvolution_apply_zero
#print axioms swapSheetInvolution_apply_one
#print axioms swapSheetInvolution_isMobiusTwist
#print axioms isSheetSwapInvolution_canonical
#print axioms swapSheetInvolution_preserves_swapG
#print axioms swapInducedComplex_sq_eq_neg_id
#print axioms swapInducedComplex_symplectic_invariant
#print axioms risingSea_colimit_modularFlow_invariance
#print axioms risingSea_colimit_modular_kms_synthesis
#print axioms risingSea_tower_propagation_modular_kms_synthesis

end InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesisAudit
