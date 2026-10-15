import InfoGeometry.Clifford.LogCFTDeRhamApexMonodromyBridge

/-!
# Audit File: LogCFTDeRhamApexMonodromyBridgeAudit

This file audits the axiomatic footprint of `compile_logcft_derham_apex_monodromy_bridge`
and all key theorems of Frontier 100 to ensure 0 sorry, 0 admit, and strictly standard foundational
Lean 4 axioms.
-/

namespace InfoGeometry.Clifford.LogCFTApex.Audit

open InfoGeometry.Clifford.LogCFTApex

#print axioms coquaternion_N_upper_sq
#print axioms coquaternion_N_lower_sq
#print axioms toMatrix_coquaternion_N_upper
#print axioms toMatrix_coquaternion_N_lower
#print axioms N_sq_zero
#print axioms N_transpose_sq_zero
#print axioms trace_N
#print axioms det2_N
#print axioms det2_N_transpose
#print axioms P_L_mul_N
#print axioms N_mul_P_R
#print axioms P_R_mul_N
#print axioms N_mul_P_L
#print axioms chiral_ladder_decomp
#print axioms chiral_ladder_transpose_decomp
#print axioms monodromy_zero
#print axioms monodromy_mul
#print axioms monodromy_pow
#print axioms monodromy_mul_inv
#print axioms monodromy_inv_mul
#print axioms det2_monodromy
#print axioms det2_monodromy_pow
#print axioms dragSoldering_apex
#print axioms det2_dragSoldering_matrix
#print axioms det2_dragSoldering
#print axioms dragSoldering_coords
#print axioms dragSoldering_P_L
#print axioms dragSoldering_P_R
#print axioms det2_dragSoldering_P_R
#print axioms e1_N_conj
#print axioms e1_N_transpose_conj
#print axioms e1_monodromy_conj
#print axioms complexMonodromy_zero_weight
#print axioms det2_complexMonodromy
#print axioms det2_complexMonodromy_zero_weight
#print axioms compile_logcft_derham_apex_monodromy_bridge

end InfoGeometry.Clifford.LogCFTApex.Audit
