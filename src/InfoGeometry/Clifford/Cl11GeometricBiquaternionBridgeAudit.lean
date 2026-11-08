import InfoGeometry.Clifford.Cl11GeometricBiquaternionBridge

/-!
# Audit File: Cl11GeometricBiquaternionBridgeAudit

This file audits the axiomatic footprint of `compile_cl11_geometric_biquaternion_bridge`
to ensure 0 sorry, 0 admit, and strictly standard foundational Lean 4 axioms.
-/

namespace InfoGeometry.Clifford.GeometricBiquaternion.Audit

open InfoGeometry.Clifford.GeometricBiquaternion.Biquat

#print axioms I3_sq
#print axioms I3_comm_coquaternion
#print axioms E3_sq
#print axioms I3_mul_E1_sq
#print axioms I3_mul_E2_sq
#print axioms I3_mul_Omega_sq
#print axioms J_spinor_sq
#print axioms anticomm_J_Gamma
#print axioms toMatrix4_mul
#print axioms J4_sq
#print axioms compile_cl11_geometric_biquaternion_bridge

end InfoGeometry.Clifford.GeometricBiquaternion.Audit
