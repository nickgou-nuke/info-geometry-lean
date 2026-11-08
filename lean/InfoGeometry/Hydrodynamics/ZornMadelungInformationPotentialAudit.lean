import InfoGeometry.Hydrodynamics.ZornMadelungInformationPotential

/-!
# Audit Companion for Zorn Vector Matrix Algebra & Madelung Information Potential

Module: `InfoGeometry.Hydrodynamics.ZornMadelungInformationPotentialAudit`

This module audits the axiomatic footprint of all theorems in
`ZornMadelungInformationPotential.lean`.
-/

namespace InfoGeometry.Hydrodynamics.ZornMadelung.Audit

open InfoGeometry.Hydrodynamics.ZornMadelung

-- Section 1: Vec3 Cross-Term Cancellation
#print axioms Vec3.dot_comm
#print axioms Vec3.dot_add_sub_cancel

-- Section 2: Zorn Determinant Decomposition & Incompressible Balance
#print axioms ZornMatrix.zorn_potential_det_split
#print axioms ZornMatrix.zorn_kinetic_fisher_balance

-- Section 3: Bohm-Fisher Potential Relations
#print axioms bohm_potential_is_fisher_gradient
#print axioms bohm_potential_balance

-- Section 4: Master Verification Certificate
#print axioms compile_zorn_madelung_potential

end InfoGeometry.Hydrodynamics.ZornMadelung.Audit
