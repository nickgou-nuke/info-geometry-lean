/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.UnorientedSuperGrassmannianCPT

/-!
# Unoriented Super-Grassmannian CPT Audit

Kernel audit verifying:
1. `P_involutive`, `C_involutive`, `T_involutive`
2. `CPT_sq_neg`
3. `charge_conjugation_swaps_sheets`
4. `charge_conjugation_swaps_vacuum_to_primal`
5. `moebiusTwist_involutive`
6. `moebius_anticommutes_paraK`
7. `kreinForm_cpt_anti_invariant`
8. `symplecticForm_cpt_invariant`
9. `kreinForm_charge_conjugation_invariant`
-/

namespace InfoGeometry.SuperGrassmannian.ModularCPT.Audit

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (pairing : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
variable (h_symm : ∀ x y : E, pairing x y = pairing y x)

#print axioms P_involutive
#print axioms C_involutive
#print axioms T_involutive
#print axioms K_involutive
#print axioms CPT_sq_neg
#print axioms CPT_eq_neg_K_comp_C
#print axioms C_anticomm_K
#print axioms charge_conjugation_swaps_sheets
#print axioms charge_conjugation_swaps_vacuum_to_primal
#print axioms moebiusTwist_involutive
#print axioms moebius_anticommutes_paraK
#print axioms kreinForm_cpt_anti_invariant
#print axioms symplecticForm_cpt_invariant
#print axioms kreinForm_charge_conjugation_invariant
#print axioms kreinForm_K_anti_invariant

end InfoGeometry.SuperGrassmannian.ModularCPT.Audit
