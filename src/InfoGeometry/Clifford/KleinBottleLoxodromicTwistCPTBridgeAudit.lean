import InfoGeometry.Clifford.KleinBottleLoxodromicTwistCPTBridge

/-!
# Audit File: KleinBottleLoxodromicTwistCPTBridgeAudit

This file audits the axiomatic footprint of `compile_klein_bottle_loxodromic_twist_cpt_bridge`
and all key theorems of Frontier 98 to ensure 0 sorry, 0 admit, and strictly standard foundational
Lean 4 axioms.
-/

namespace InfoGeometry.Clifford.KleinBottleLoxodromicTwist.Audit

open InfoGeometry.Clifford.KleinBottleLoxodromicTwist

#print axioms e1_sq_one
#print axioms e1_transpose
#print axioms det2_e1
#print axioms chiral_swap_P_L_to_P_R
#print axioms chiral_swap_P_R_to_P_L
#print axioms soldering_parity_reflection
#print axioms det2_e1_conj
#print axioms det2_soldering_parity_invariant
#print axioms det2_solderingMatrix_parity
#print axioms boostX_transpose
#print axioms e1_boostX_e1
#print axioms boostX_mul
#print axioms boostX_sq
#print axioms glide_reflection_sq_dilation
#print axioms spinor_twist_pi_half
#print axioms spinor_twist_pi_half_complex
#print axioms compile_klein_bottle_loxodromic_twist_cpt_bridge

end InfoGeometry.Clifford.KleinBottleLoxodromicTwist.Audit
