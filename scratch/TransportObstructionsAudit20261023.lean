/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.PeirceToCircularBridge
import InfoGeometry.Algebra.ChiralCARTransport
import InfoGeometry.Algebra.InvariantTransport
import InfoGeometry.Algebra.ChiralRealHyperbolicRotor

-- Contract: ring-hom transport of commuting units; real-star preservation of
-- hyperbolic sandwiches on odd self-adjoint operators. No Spin/Pin classification.
#print axioms InfoGeometry.Algebra.InvariantTransport.anticommutator_eq_zero_iff_of_commute_of_isUnit
#print axioms InfoGeometry.Algebra.InvariantTransport.map_anticommutator_eq_zero_iff_of_commute_of_isUnit
#print axioms InfoGeometry.Algebra.InvariantTransport.map_anticommutator_ne_zero_of_commute_of_isUnit
#print axioms InfoGeometry.OperatorAlgebra.hyperbolicRotor_conjugate_of_anticommute
#print axioms InfoGeometry.OperatorAlgebra.hyperbolicRotor_conjugate_star_defect
#print axioms InfoGeometry.OperatorAlgebra.hyperbolicRotor_conjugate_selfAdjoint_iff

#print axioms InfoGeometry.Algebra.ChiralCARTransport.quadratic_commutator
#print axioms InfoGeometry.Algebra.ChiralCARTransport.cross_current_commutes_left
#print axioms InfoGeometry.Algebra.ChiralCARTransport.pairing_current_commutator_annihilator
#print axioms InfoGeometry.Algebra.ChiralCARTransport.pairing_current_commutator_creator
#print axioms InfoGeometry.Algebra.ChiralCARTransport.pairing_current_star

#print axioms InfoGeometry.CliffordWeyl.PeirceToCircularBridge.qwp_operator_state_intertwining

#print axioms InfoGeometry.CliffordWeyl.PeirceToCircularBridge.qwpHorizontalJones_eq_counterclockwise

#print axioms InfoGeometry.CliffordWeyl.PeirceToCircularBridge.qwp_adjoint_horizontal_eq_clockwise
