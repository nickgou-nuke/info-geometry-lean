/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge

/-!
# Audit Companion for `Cl22LightconeWeylBerezinGaugeBridge`

Verifies signature availability and standard Lean 4 axiomatic footprint
for the $\mathrm{Cl}(2,2)$ paracomplex-lightcone basis transition, reciprocal
$\lambda \leftrightarrow \lambda^{-1}$ dual $\mathrm{Cl}(1,1)$ CAR scaling,
trace/determinant separation, and Chiral Berezinian Weyl gauge invariance.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridgeAudit

open InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge

#check @J_geom_mul_omega1_ne_comm
#check @J_geom_anticomm_omega1
#check @stdBivectorBlock_eq_lightconePeircianBlock
#check @lightconePeircianBlock_eq_stdBivectorBlock
#check @J_geom_intertwines_and_swaps_peircian_projectors
#check @weylScaledMajorana_sq_zero
#check @weylScaledMajorana_car_invariant
#check @logTimeMajorana_car_invariant
#check @cl22_nontrivial_modes_traceless
#check @weylScaledMultivector_trace_eq
#check @n_plus_minus_1_anticomm_e3
#check @weylScaledSolderedVector_sq_invariant
#check @weylScaledSolderedVector_has_two_sided_inverse
#check @lightconeGramMatrix_det_weyl_invariant
#check @berezinianSchur_weyl_gauge_invariant
#check @logTimeBerezinianSchur_eq_const
#check @deriv_logTimeBerezinianSchur_eq_zero
#check @berezinian_super_lu_weyl_invariant

#print axioms J_geom_mul_omega1_ne_comm
#print axioms stdBivectorBlock_eq_lightconePeircianBlock
#print axioms J_geom_intertwines_and_swaps_peircian_projectors
#print axioms weylScaledMajorana_car_invariant
#print axioms logTimeMajorana_car_invariant
#print axioms weylScaledMultivector_trace_eq
#print axioms weylScaledSolderedVector_sq_invariant
#print axioms weylScaledSolderedVector_has_two_sided_inverse
#print axioms lightconeGramMatrix_det_weyl_invariant
#print axioms berezinianSchur_weyl_gauge_invariant
#print axioms logTimeBerezinianSchur_eq_const
#print axioms deriv_logTimeBerezinianSchur_eq_zero
#print axioms berezinian_super_lu_weyl_invariant

end InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridgeAudit
