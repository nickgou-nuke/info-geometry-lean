import InfoGeometry.NuclearPhysics.NuclearQuasiphononKreinSUSY

/-!
# Audit Companion for Section 87: Nuclear Quasiphonon Krein-SUSY Intertwining & Soloviev Pairing Architecture

This module audits the axiomatic footprint of all theorems in
`InfoGeometry.NuclearPhysics.NuclearQuasiphononKreinSUSY`.
-/

namespace InfoGeometry.NuclearPhysics.NuclearQuasiphononKreinSUSY.Audit

open InfoGeometry.NuclearPhysics.NuclearQuasiphononKreinSUSY

-- Section 2: Quasiphonon Ladder Operator Identification & CAR
#print axioms car_alpha
#print axioms car_beta

-- Section 3: Soloviev Pairing Hamiltonian as an Inner Derivation
#print axioms T_pair_explicit
#print axioms T_pair_comm_H
#print axioms H_gen_as_sum

-- Section 4: Krein Metric & Paracomplex Sheet-Swap Intertwining
#print axioms J_sheet_sq
#print axioms eta_krein_sq
#print axioms J_sheet_tau1_J_sheet
#print axioms J_sheet_inverts_H

-- Section 5: Krein Self-Adjointness
#print axioms T_pair_krein_self_adjoint
#print axioms H_gen_krein_self_adjoint
#print axioms tau1_krein_self_adjoint

-- Section 6: Soloviev Pairing Hamiltonian & BdG Dispersion
#print axioms pairing_krein_self_adjoint
#print axioms pairing_sheet_swap_intertwine
#print axioms pairing_hamiltonian_sq
#print axioms pairing_hamiltonian_cube
#print axioms pairing_supertrace

-- Section 7: Master Certification & Conjunction Targets
#print axioms compile_nuclear_quasiphonon_krein_susy_cert
#print axioms compile_nuclear_quasiphonon_krein_susy

end InfoGeometry.NuclearPhysics.NuclearQuasiphononKreinSUSY.Audit
