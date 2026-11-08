import InfoGeometry.Clifford.ConformalProjectiveBoundaryCasimirBridge

/-!
# Audit File: ConformalProjectiveBoundaryCasimirBridgeAudit

This file audits the axiomatic footprint of `compile_conformal_projective_boundary_casimir_bridge`
to ensure 0 sorry, 0 admit, and strictly standard foundational Lean 4 axioms.
-/

namespace InfoGeometry.Clifford.ConformalBoundary.Audit

open InfoGeometry.Clifford.ConformalBoundary

#print axioms trace2_solderingMatrix
#print axioms trace2_add
#print axioms trace2_zero
#print axioms trace2_dilate
#print axioms det2_dilate
#print axioms celestial_boundary_dilation_invariant
#print axioms mul_adj2
#print axioms adj2_mul
#print axioms det2_adj2
#print axioms adj2_null_is_null
#print axioms conformal_casimir_transform
#print axioms conformal_casimir_boundary_zero
#print axioms trace2_P_L
#print axioms trace2_P_R
#print axioms trace2_neg_P_L
#print axioms trace2_neg_P_R
#print axioms det2_neg_P_L
#print axioms det2_neg_P_R
#print axioms trace2_chiral_difference
#print axioms compile_conformal_projective_boundary_casimir_bridge

end InfoGeometry.Clifford.ConformalBoundary.Audit
