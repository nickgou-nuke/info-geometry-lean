/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinBottleKMSKeldyshWalsh

/-!
# Axiom Audit for KleinBottleKMSKeldyshWalsh

Verifies via `#print axioms` that all exported theorems in
`InfoGeometry.Topology.KleinBottleKMSKeldyshWalsh` depend exclusively
on Lean 4's foundational axioms (`propext`, `Quot.sound`, `Classical.choice`),
with zero `sorry`, `admit`, `native_decide`, or custom axioms.
-/

open InfoGeometry.Topology.KleinBottleKMSKeldyshWalsh

#print axioms matE01_mul_E10_ne_mul_E10_E01
#print axioms kmsGlide_sq
#print axioms kmsGlide_fixedPointFree_iff
#print axioms kmsGlide_sq_and_fixedPointFree_iff
#print axioms kmsGlide_jacobian_det_neg_one
#print axioms kmsGlide_timeShift_relation
#print axioms kmsKleinHom_apply_genA
#print axioms kmsKleinHom_apply_genB
#print axioms kmsKleinHom_wellDefined
#print axioms kmsKleinHom_nontrivial_witness
#print axioms involution_conjugation_neg_iff_anticomm
#print axioms cl11_Eplus_conjugates_J1_to_neg
#print axioms cl11_Eplus_J1_anticomm
#print axioms peirce_invS_sq
#print axioms peirce_invS_genPhi_anticomm
#print axioms peirce_invS_conjugates_genPhi_to_neg
#print axioms keldysh45Mat_sq
#print axioms keldysh45Mat_intertwines_J1_Eplus
#print axioms keldysh45Mat_walsh_krein_intertwining
#print axioms cl11_J1_Eplus_noncommutative
#print axioms cl11_J1_Eplus_noncommutative_witness
#print axioms klein_circle_inversion_countermodel_link
