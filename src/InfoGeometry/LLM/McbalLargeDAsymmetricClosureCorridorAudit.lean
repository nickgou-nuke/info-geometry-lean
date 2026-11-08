/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor

/-!
# Axiom Audit for `McbalLargeDAsymmetricClosureCorridor`

Exposes the kernel axiom dependencies of the three-post `mcbal.github.io` kinetic vector-spin
corridor and the 8-stage `solve et coagula` sequence-modeling-to-LogCFT poset
(`McbalToKreinYangianLogCFTStage`, $\mathfrak{M}_1 \prec \dots \prec \mathfrak{M}_8$).
-/

open InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor

#print axioms McbalToKreinYangianLogCFTStage.poset_root_diamond_and_terminal
#print axioms mcbal_matrix_units_noncommute
#print axioms mcbal_post1_largeD_vmf_response_norm_and_inverse_recovery
#print axioms mcbal_post1_singleSpinCovarianceOp_spectral_and_mul
#print axioms mcbal_post2_prenorm_residual_bus_and_quench_relax_entropy_budget
#print axioms stageM2_stochastic_drazin_index_one_semisimplicity_aporia
#print axioms mcbal_post3_exact_sphere_norm_conservation
#print axioms mcbal_post3_three_level_closure_hierarchy_k1_vs_k2_defect
#print axioms stageM3_noncommutative_covariance_closure_and_gain_defect
#print axioms stageM4_multihop_word_nonclosure
#print axioms stagesM5_M6_cl11_tower_sonn_and_yangian_monodromy
#print axioms stagesM7_M8_krein_exceptional_isotropy_and_logcft_secular_evolution
#print axioms mcbal_to_krein_yangian_logcft_master_synthesis
