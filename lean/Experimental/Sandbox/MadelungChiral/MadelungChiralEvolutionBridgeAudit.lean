import Experimental.Sandbox.MadelungChiral.MadelungChiralEvolutionBridge

/-!
# Audit Companion for Discrete Madelung Chiral Evolution Bridge

This module audits the axiomatic footprint of all theorems in
`MadelungChiralEvolutionBridge.lean`.
-/

namespace InfoGeometry.Experimental.MadelungChiral.Audit

open InfoGeometry.Experimental.MadelungChiral

-- Section 1
#print axioms edgeCurrent_antisymm
#print axioms edgeCurrent_self_zero

-- Section 2
#print axioms scalar_I_mul_rev_sub_I_mul
#print axioms densityRate_eq_sum_edgeCurrent
#print axioms discrete_continuity_equation
#print axioms total_norm_conservation
#print axioms fisher_rao_amplitude_isometry

-- Section 3
#print axioms P_plus_sq
#print axioms P_minus_sq
#print axioms P_plus_mul_P_minus
#print axioms P_minus_mul_P_plus
#print axioms P_plus_add_P_minus
#print axioms chiral_odd_diagonal_corners_zero
#print axioms chiral_odd_inter_sheet_coupling

-- Section 4
#print axioms density_rotor_gauge_invariant
#print axioms edgeCurrent_rotor_gauge_invariant
#print axioms schrodinger_commutes_rotorGaugeTransform

-- Section 5
#print axioms normalized_trace_doubling_invariant

-- Section 6
#print axioms compile_madelung_chiral_evolution

end InfoGeometry.Experimental.MadelungChiral.Audit

