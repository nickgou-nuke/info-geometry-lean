import Experimental.Sandbox.SuperGrassmannian.MajoranaCARSuperalgebra

/-!
# Axiomatic Audit for Majorana CAR Superalgebra and Chiral Grading

Module: `InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebraAudit`

This companion module audits the axiomatic footprint of all theorems in
`MajoranaCARSuperalgebra.lean`.

All theorems must depend ONLY on the core Lean 4 foundation:
- Pure algebraic identities depend on `[propext]` or empty `[]`.
- No theorem may depend on `sorryAx` or custom axioms.
-/

namespace InfoGeometry.SuperGrassmannian.MajoranaCAR.Audit

open InfoGeometry.SuperGrassmannian.MajoranaCAR
open InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell

-- Section 1: Split Clifford Cell Structure Cl(1,1)
#print axioms e_sq_one
#print axioms f_sq_neg_one
#print axioms ef_anticomm_zero
#print axioms e_mul_e
#print axioms f_mul_f
#print axioms fe_eq_neg_ef
#print axioms ef_eq_neg_fe
#print axioms two_mul_half
#print axioms half_mul_two
#print axioms half_sq_mul_four

-- Section 2: Majorana CAR Ladder Operators & Nilpotent Lightcone Modes
#print axioms a_mul_a
#print axioms a_sq_zero
#print axioms a_star_mul_a_star
#print axioms a_star_sq_zero
#print axioms car_anticommutator
#print axioms a_mul_a_star_eq

-- Section 3: Chiral Grading Operator & Odd Parity
#print axioms Gamma_mul_Gamma
#print axioms Gamma_sq
#print axioms Gamma_mul_a
#print axioms a_mul_Gamma
#print axioms Gamma_anticomm_a
#print axioms Gamma_mul_a_star
#print axioms a_star_mul_Gamma
#print axioms Gamma_anticomm_a_star

-- Section 4: Number and Vacuum Projectors & Orthogonal Annihilation
#print axioms N_mul_N
#print axioms N_sq
#print axioms vac_proj_sq
#print axioms ortho_annihilation
#print axioms ortho_annihilation_left
#print axioms N_eq_half_one_add_Gamma
#print axioms two_mul_N
#print axioms Gamma_eq_two_N_sub_one
#print axioms parity_reflection_fe
#print axioms vac_parity_reflection

-- Section 5: Quantum Ladder Dynamics & Vacuum Annihilation
#print axioms N_mul_a
#print axioms a_mul_N
#print axioms ladder_bracket_N_a
#print axioms a_star_mul_N
#print axioms N_mul_a_star
#print axioms ladder_bracket_N_a_star
#print axioms a_mul_vac_proj
#print axioms vac_proj_mul_a_star
#print axioms N_mul_Gamma
#print axioms Gamma_mul_N
#print axioms bracket_N_Gamma

-- Section 6: Master Verification Certificate
#print axioms compile_majorana_car_superalgebra

end InfoGeometry.SuperGrassmannian.MajoranaCAR.Audit
