import InfoGeometry.Clifford.OperatorKleinTomitaCPTBridge

/-!
# Audit File: OperatorKleinTomitaCPTBridgeAudit

This file audits the axiomatic footprint of `compile_operator_klein_tomita_cpt_bridge`
and all key operator-algebraic theorems of Frontier 99 to ensure 0 sorry, 0 admit,
and strictly standard foundational Lean 4 axioms.
-/

namespace InfoGeometry.Clifford.OperatorKleinTomitaCPT.Audit

open InfoGeometry.Clifford.OperatorKleinTomitaCPT

#print axioms tomita_klein_monodromy_relation
#print axioms tomita_klein_monodromy_reverse
#print axioms operatorGlide_sq
#print axioms cylinderGlide_sq
#print axioms chiral_swap_left_ideal
#print axioms chiral_swap_right_ideal
#print axioms chiral_swap_right_projector_left_ideal
#print axioms chiral_swap_right_projector_right_ideal
#print axioms fermion_spin_flip_graded
#print axioms boson_spin_graded
#print axioms operator_curvature_cpt_negation
#print axioms compile_operator_klein_tomita_cpt_bridge

end InfoGeometry.Clifford.OperatorKleinTomitaCPT.Audit
